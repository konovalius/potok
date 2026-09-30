/*
  «Поток» — закрытый общий чат. Логика клиента.
  Транспорт: приватная база Supabase (анонимная сессия + код доступа + защита на уровне строк).
  Сквозное шифрование: сообщения шифруются на устройстве (AES-GCM; ключ выводится из кода доступа) —
  база хранит только шифротекст.
*/
(() => {
  'use strict';

  // ── Конфигурация ────────────────────────────────────────────
  const CONF = window.POTOK_CONFIG || {};
  const sb = (window.supabase && CONF.supabaseUrl && CONF.supabaseAnonKey)
    ? window.supabase.createClient(CONF.supabaseUrl, CONF.supabaseAnonKey)
    : null;

  const DEFAULT_ROOM = 'общий';
  const MAX_TEXT = 600;         // с шифрованием сообщение занимает больше места в базе
  const E2E_PREFIX = 'e2e1:';   // метка шифрованного сообщения
  const E2E_SALT = 'potok.e2e.v1';
  const E2E_ITER = 210000;
  const CACHE_LIMIT = 80;
  const DOM_LIMIT = 300;
  const HISTORY_LIMIT = 300;
  const GROUP_WINDOW = 5 * 60 * 1000; // 5 минут — окно склейки сообщений одного автора
  const LIVE_WINDOW = 60 * 1000;      // старше минуты — считаем историей (без звука и счётчика)
  const LS = { name: 'potok.v1.name', sound: 'potok.v1.sound', room: 'potok.v1.room', key: 'potok.v3.key' };
  const CACHE_PREFIX = 'potok.v2.cache.';

  // ── Состояние ───────────────────────────────────────────────
  const state = {
    name: '',
    sound: true,
    room: DEFAULT_ROOM,
    seen: new Set(),        // id сообщений (строк базы), уже отрисованных
    pending: new Map(),     // client_msg_id -> { el, st, text, time, failed, reconciled }
    msgEls: new Map(),      // id сообщения -> DOM-узел строки (для удаления)
    unread: 0,
    msgCount: 0,
    lastDay: '',
    lastAuthor: '',
    lastTime: 0,
    joined: false,
    dmPeer: null,
    baseTitle: 'Поток — общий чат'
  };

  let channel = null;        // realtime-канал текущей комнаты
  let currentUser = null;    // текущий пользователь сессии (для «моё/не моё»)
  let cryptoKey = null;      // ключ шифрования (CryptoKey), выведен из кода доступа
  let loadTimer = null;
  let slowTimer = null;
  let audioCtx = null;

  // ── Помощники ───────────────────────────────────────────────
  const $ = (id) => document.getElementById(id);
  const el = (tag, cls, text) => {
    const n = document.createElement(tag);
    if (cls) n.className = cls;
    if (text != null) n.textContent = text;
    return n;
  };
  const reducedMotion = () => window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  const safeGet = (k) => { try { return localStorage.getItem(k); } catch (e) { return null; } };
  const safeSet = (k, v) => { try { localStorage.setItem(k, v); } catch (e) { /* приватный режим — переживём */ } };
  const safeSGet = (k) => { try { return sessionStorage.getItem(k); } catch (e) { return null; } };
  const safeSSet = (k, v) => { try { sessionStorage.setItem(k, v); } catch (e) {} };

  // Ключи комнат для кэша/каналов (в комнатах допустимы любые буквы — оставляем слаг для единообразия)
  const TRANSLIT = { а:'a',б:'b',в:'v',г:'g',д:'d',е:'e',ё:'e',ж:'zh',з:'z',и:'i',й:'y',к:'k',л:'l',м:'m',н:'n',о:'o',п:'p',р:'r',с:'s',т:'t',у:'u',ф:'f',х:'h',ц:'c',ч:'ch',ш:'sh',щ:'sch',ъ:'',ы:'y',ь:'',э:'e',ю:'yu',я:'ya' };
  function slugifyRoom(label) {
    let out = '';
    for (const ch of String(label).toLowerCase()) {
      if (/[a-z0-9_-]/.test(ch)) out += ch;
      else if (TRANSLIT[ch] != null) out += TRANSLIT[ch];
      else out += '-';
    }
    out = out.replace(/-+/g, '-').replace(/^-|-$/g, '').slice(0, 48);
    return out || 'room';
  }
  function normalizeRoom(raw) {
    let label = String(raw || '').trim().replace(/\s+/g, ' ');
    if (label.length > 32) label = label.slice(0, 32);
    if (!label || label.toLowerCase() === DEFAULT_ROOM) label = DEFAULT_ROOM;
    return label;
  }

  // Имя по умолчанию: «Гость-Сова» и т.п. — стабильно для устройства, без вопросов
  const GUEST_WORDS = ['Сова', 'Лис', 'Ёж', 'Кот', 'Барсук', 'Выдра', 'Грач', 'Дрозд', 'Олень', 'Хорёк', 'Соболь', 'Филин'];
  function defaultGuestName() {
    let seed = (currentUser && currentUser.id) || safeGet('potok.v1.seed');
    if (!seed) { seed = String(Math.random()) + String(Date.now()); safeSet('potok.v1.seed', seed); }
    let h = 0;
    for (let i = 0; i < seed.length; i++) h = (h * 31 + seed.charCodeAt(i)) | 0;
    return 'Гость-' + GUEST_WORDS[Math.abs(h) % GUEST_WORDS.length];
  }

  // «Моё» сообщение определяем по user_id сессии (надёжнее, чем сравнение имён)
  function isMine(userId, name) {
    if (userId && currentUser && currentUser.id) return userId === currentUser.id;
    return (name || '') === state.name;
  }

  // ── Сквозное шифрование (E2E) ───────────────────────────────
  function bufToB64(buf) {
    const b = new Uint8Array(buf);
    let s = '';
    for (let i = 0; i < b.length; i++) s += String.fromCharCode(b[i]);
    return btoa(s);
  }
  function b64ToBuf(b64) {
    const s = atob(b64);
    const b = new Uint8Array(s.length);
    for (let i = 0; i < s.length; i++) b[i] = s.charCodeAt(i);
    return b;
  }
  async function deriveKeyBits(code) {
    const enc = new TextEncoder();
    const base = await crypto.subtle.importKey('raw', enc.encode(code), 'PBKDF2', false, ['deriveBits']);
    const bits = await crypto.subtle.deriveBits({ name: 'PBKDF2', salt: enc.encode(E2E_SALT), iterations: E2E_ITER, hash: 'SHA-256' }, base, 256);
    return new Uint8Array(bits);
  }
  async function importCryptoKey(bits) {
    return crypto.subtle.importKey('raw', bits, { name: 'AES-GCM' }, false, ['encrypt', 'decrypt']);
  }
  async function setUpKey(code) {
    const bits = await deriveKeyBits(code);
    cryptoKey = await importCryptoKey(bits);
    safeSet(LS.key, bufToB64(bits));
  }
  async function loadStoredKey() {
    if (cryptoKey) return true;
    const stored = safeGet(LS.key);
    if (!stored) return false;
    try { cryptoKey = await importCryptoKey(b64ToBuf(stored)); return true; }
    catch (e) { cryptoKey = null; return false; }
  }
  async function encryptPayload(obj) {
    if (!cryptoKey) throw new Error('no-key');
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const ct = await crypto.subtle.encrypt({ name: 'AES-GCM', iv }, cryptoKey, new TextEncoder().encode(JSON.stringify(obj)));
    const out = new Uint8Array(iv.length + ct.byteLength);
    out.set(iv, 0);
    out.set(new Uint8Array(ct), iv.length);
    return E2E_PREFIX + bufToB64(out);
  }
  async function decryptPayload(body) {
    const src = String(body || '');
    if (src.indexOf(E2E_PREFIX) !== 0) return { t: src, n: null, plain: true, failed: false };
    try {
      if (!cryptoKey) throw new Error('no-key');
      const buf = b64ToBuf(src.slice(E2E_PREFIX.length));
      const iv = buf.slice(0, 12);
      const ct = buf.slice(12);
      const pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv }, cryptoKey, ct);
      const obj = JSON.parse(new TextDecoder().decode(pt));
      return { t: String(obj.t || ''), n: String(obj.n || ''), obj, plain: false, failed: false };
    } catch (e) {
      return { t: 'Сообщение зашифровано — нет ключа или повреждено', n: '', plain: false, failed: true };
    }
  }

  // Идентичность: цвет аватара выводится из имени — одинаков у всех участников
  function hashCode(str) { let h = 0; for (let i = 0; i < str.length; i++) h = (h * 31 + str.charCodeAt(i)) | 0; return Math.abs(h); }
  function avatarHue(name) { return Math.round((hashCode(name) * 137.508) % 360); }
  function initials(name) {
    const parts = String(name).trim().split(/\s+/).filter(Boolean);
    let s = (parts[0] && parts[0][0]) || '?';
    if (parts[1] && parts[1][0]) s += parts[1][0];
    return s.toUpperCase();
  }
  function paintAvatar(node, name) {
    if (!node) return;
    const hue = avatarHue(name || '?');
    node.style.background = 'hsl(' + hue + ' 42% 87%)';
    node.style.color = 'hsl(' + hue + ' 45% 28%)';
    node.textContent = initials(name || '?');
  }

  // Даты и время
  const timeFmt = new Intl.DateTimeFormat('ru-RU', { hour: '2-digit', minute: '2-digit' });
  const dateFmt = new Intl.DateTimeFormat('ru-RU', { day: 'numeric', month: 'long' });
  const dateYearFmt = new Intl.DateTimeFormat('ru-RU', { day: 'numeric', month: 'long', year: 'numeric' });
  const dayKey = (ms) => { const d = new Date(ms); return d.getFullYear() + '-' + d.getMonth() + '-' + d.getDate(); };
  function dayLabel(ms) {
    const d = new Date(ms);
    const now = new Date();
    const today = dayKey(now.getTime());
    const yesterday = dayKey(new Date(now.getFullYear(), now.getMonth(), now.getDate() - 1).getTime());
    const k = dayKey(ms);
    if (k === today) return 'сегодня';
    if (k === yesterday) return 'вчера';
    return (d.getFullYear() === now.getFullYear() ? dateFmt : dateYearFmt).format(d);
  }
  function plural(n) {
    const m10 = n % 10, m100 = n % 100;
    const word = (m10 === 1 && m100 !== 11) ? 'новое сообщение'
      : (m10 >= 2 && m10 <= 4 && !(m100 >= 12 && m100 <= 14)) ? 'новых сообщения'
      : 'новых сообщений';
    return n + ' ' + word;
  }

  // ── DOM ─────────────────────────────────────────────────────
  const chatScroll = $('chatScroll');
  const chatList = $('chatList');
  const skeleton = $('skeleton');
  const slowNote = $('slowNote');
  const emptyState = $('emptyState');
  const emptyCta = $('emptyCta');
  const emptyTitle = $('emptyTitle');
  const emptyTextEl = $('emptyText');
  const jumpBtn = $('jumpBtn');
  const jumpText = $('jumpText');
  const connBox = $('conn');
  const connText = $('connText');
  const offlineBanner = $('offlineBanner');
  const offlineText = $('offlineText');
  const retryBtn = $('retryBtn');
  const composerForm = $('composerForm');
  const composerInput = $('composerInput');
  const sendBtn = $('sendBtn');
  const charCounter = $('charCounter');
  const roomChip = $('roomChip');
  const roomLabelEl = $('roomLabel');
  const roomHashEl = $('roomHash');
  const backBtn = $('backBtn');
  const shareBtn = $('shareBtn');
  const meBtn = $('meBtn');
  const meAvatar = $('meAvatar');
  const meName = $('meName');
  const passGate = $('passGate');
  const passForm = $('passForm');
  const passInput = $('passInput');
  const passError = $('passError');
  const passSubmit = $('passSubmit');
  const settings = $('settings');
  const settingsForm = $('settingsForm');
  const settingsName = $('settingsName');
  const settingsNameError = $('settingsNameError');
  const soundToggle = $('soundToggle');
  const settingsClose = $('settingsClose');
  const copyLinkBtn = $('copyLinkBtn');
  const logoutBtn = $('logoutBtn');
  const toasts = $('toasts');

  // ── Звук ────────────────────────────────────────────────────
  function ensureAudio() {
    try {
      if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
      if (audioCtx.state === 'suspended') audioCtx.resume();
    } catch (e) { audioCtx = null; }
  }
  function blip() {
    if (!state.sound) return;
    try {
      ensureAudio();
      if (!audioCtx || audioCtx.state !== 'running') return;
      const t = audioCtx.currentTime;
      const o = audioCtx.createOscillator();
      const g = audioCtx.createGain();
      o.type = 'sine';
      o.frequency.setValueAtTime(660, t);
      o.frequency.exponentialRampToValueAtTime(920, t + 0.09);
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(0.055, t + 0.02);
      g.gain.exponentialRampToValueAtTime(0.0001, t + 0.16);
      o.connect(g).connect(audioCtx.destination);
      o.start(t); o.stop(t + 0.18);
    } catch (e) { /* звук — опция, не критично */ }
  }

  // ── Тосты ───────────────────────────────────────────────────
  function toast(text, onClick) {
    const t = el('div', 'toast' + (onClick ? ' toast-click' : ''), text);
    let hideTimer = setTimeout(hide, onClick ? 5200 : 3400);
    function hide() { t.classList.add('out'); setTimeout(() => t.remove(), 220); }
    t.addEventListener('mouseenter', () => clearTimeout(hideTimer));
    t.addEventListener('focusin', () => clearTimeout(hideTimer));
    t.addEventListener('mouseleave', () => { hideTimer = setTimeout(hide, 1200); });
    if (onClick) {
      t.addEventListener('click', () => { clearTimeout(hideTimer); t.remove(); onClick(); });
      t.setAttribute('role', 'button');
      t.tabIndex = 0;
      t.addEventListener('keydown', (e) => {
        if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); clearTimeout(hideTimer); t.remove(); onClick(); }
      });
    }
    toasts.appendChild(t);
  }

  // ── Прокрутка и непрочитанные ───────────────────────────────
  function isNearBottom() {
    return chatScroll.scrollHeight - chatScroll.scrollTop - chatScroll.clientHeight < 140;
  }
  function scrollToBottom(behavior) {
    chatScroll.scrollTo({ top: chatScroll.scrollHeight, behavior: reducedMotion() ? 'auto' : (behavior || 'smooth') });
  }
  function updateUnreadUI() {
    const n = state.unread;
    document.title = n > 0 ? '(' + n + ') ' + state.baseTitle : state.baseTitle;
    if (n > 0 && !isNearBottom()) {
      jumpText.textContent = plural(n);
      jumpBtn.hidden = false;
    } else {
      jumpBtn.hidden = true;
    }
  }
  let scrollTick = false;
  chatScroll.addEventListener('scroll', () => {
    if (scrollTick) return;
    scrollTick = true;
    requestAnimationFrame(() => {
      scrollTick = false;
      if (isNearBottom() && state.unread > 0) state.unread = 0;
      updateUnreadUI();
    });
  }, { passive: true });
  jumpBtn.addEventListener('click', () => { state.unread = 0; scrollToBottom('smooth'); updateUnreadUI(); });

  document.addEventListener('visibilitychange', () => {
    if (!document.hidden && isNearBottom() && state.unread > 0) { state.unread = 0; }
    if (!document.hidden) updateUnreadUI();
  });

  // ── Статус соединения и баннер ──────────────────────────────
  const CONN_TEXT = { connecting: 'подключение…', online: 'в сети', reconnecting: 'переподключение…', error: 'нет связи' };
  function setConn(mode) {
    connBox.dataset.state = mode;
    connText.textContent = CONN_TEXT[mode] || mode;
  }
  function showBanner(text) { offlineText.textContent = text; offlineBanner.hidden = false; }
  function hideBanner() { offlineBanner.hidden = true; }

  // ── Пустая комната / скелетон ───────────────────────────────
  function removeSkeleton() {
    if (!skeleton.hidden) skeleton.hidden = true;
    if (!slowNote.hidden) slowNote.hidden = true;
  }
  function maybeShowEmpty() {
    if (state.msgCount === 0 && skeleton.hidden) emptyState.hidden = false;
  }
  function hideEmpty() { if (!emptyState.hidden) emptyState.hidden = true; }

  // ── Кэш сообщений (мгновенная отрисовка) ────────────────────
  const cacheKey = () => CACHE_PREFIX + slugifyRoom(state.room);
  function loadCache() {
    try {
      const raw = safeGet(cacheKey());
      const arr = raw ? JSON.parse(raw) : [];
      return Array.isArray(arr) ? arr : [];
    } catch (e) { return []; }
  }
  function addToCache(item) {
    try {
      const arr = loadCache();
      if (arr.some((m) => m.id === item.id)) return;
      arr.push(item);
      while (arr.length > CACHE_LIMIT) arr.shift();
      safeSet(cacheKey(), JSON.stringify(arr));
    } catch (e) { /* кэш — оптимизация */ }
  }

  // ── Отрисовка сообщений ─────────────────────────────────────
  function linkifyInto(node, text) {
    const re = /https?:\/\/[^\s<>"']+/gi;
    let last = 0, m;
    while ((m = re.exec(text))) {
      let url = m[0];
      let trail = '';
      const tm = url.match(/[)\].,!?;:]+$/);
      if (tm) { trail = tm[0]; url = url.slice(0, -trail.length); }
      if (url.length > 8) {
        if (m.index > last) node.appendChild(document.createTextNode(text.slice(last, m.index)));
        const a = el('a', null, url);
        a.href = url; a.target = '_blank'; a.rel = 'noopener noreferrer nofollow';
        node.appendChild(a);
        if (trail) node.appendChild(document.createTextNode(trail));
        last = m.index + m[0].length;
      }
    }
    if (last < text.length) node.appendChild(document.createTextNode(text.slice(last)));
  }

  function trimDom() {
    while (state.msgCount > DOM_LIMIT) {
      const first = chatList.firstElementChild;
      if (!first) return;
      if (first.classList.contains('msg')) {
        if (first.classList.contains('msg-pending') || first.classList.contains('msg-error')) return; // не выкидываем «живые» сообщения
        if (first.dataset.mid) state.msgEls.delete(first.dataset.mid);
        first.remove(); state.msgCount--;
      } else if (first.classList.contains('day') || first.classList.contains('note')) {
        first.remove();
      } else {
        return;
      }
    }
  }

  function renderMessage(msg) {
    const { name, text, time, mine, id, userId } = msg;
    hideEmpty();

    const dk = dayKey(time);
    if (dk !== state.lastDay) {
      state.lastDay = dk;
      state.lastAuthor = '';
      state.lastTime = 0;
      const day = el('div', 'day');
      day.textContent = dayLabel(time);
      chatList.appendChild(day);
    }

    const grouped = state.lastAuthor === name && (time - state.lastTime) < GROUP_WINDOW && state.lastAuthor !== '';
    state.lastAuthor = name;
    state.lastTime = time;

    const cls = 'msg ' + (mine ? 'mine' : 'other') + (grouped ? ' grouped' : '') + (msg.pending ? ' msg-pending' : '') + (msg.failed ? ' msg-error' : '') + (msg.noAnim ? ' no-anim' : '');
    const row = el('div', cls);

    if (!mine) {
      const av = el('span', 'avatar');
      paintAvatar(av, name);
      av.setAttribute('aria-hidden', 'true');
      row.appendChild(av);
    }

    const wrap = el('div', 'bubble-wrap');
    if (!grouped) {
      const head = el('div', 'msg-head');
      if (!mine && userId && currentUser && userId !== currentUser.id) {
        const nameBtn = el('button', 'msg-name msg-name-btn', name);
        nameBtn.type = 'button';
        nameBtn.title = 'Написать личное сообщение';
        nameBtn.addEventListener('click', () => openDM(userId, name));
        head.appendChild(nameBtn);
      } else {
        head.appendChild(el('span', 'msg-name', name));
      }
      head.appendChild(el('span', 'msg-time', timeFmt.format(new Date(time))));
      wrap.appendChild(head);
    }
    const bubble = el('div', 'bubble' + (msg.locked ? ' locked' : ''));
    linkifyInto(bubble, String(text));
    wrap.appendChild(bubble);

    let st = null;
    if (msg.pending) {
      st = el('span', 'msg-status');
      st.appendChild(el('span', 'dot-spin'));
      st.appendChild(el('span', null, 'отправляется'));
      wrap.appendChild(st);
    }
    row.appendChild(wrap);
    chatList.appendChild(row);
    state.msgCount++;
    trimDom();

    if (id != null && !msg.pending) attachMessageId(row, id);

    if (msg.pending || isNearBottom()) {
      requestAnimationFrame(() => scrollToBottom(msg.pending ? 'smooth' : 'auto'));
    }
    return { row, st };
  }

  function setStatusNode(p, mode) {
    if (!p.st || !p.st.isConnected) return;
    p.st.textContent = '';
    if (mode === 'pending') {
      p.st.appendChild(el('span', 'dot-spin'));
      p.st.appendChild(el('span', null, 'отправляется'));
    } else if (mode === 'failed') {
      const btn = el('button', 'msg-retry', 'не отправлено · повторить');
      btn.type = 'button';
      btn.addEventListener('click', () => retryMessage(p.id));
      p.st.appendChild(btn);
    }
  }

  // ── Удаление сообщений (строки удаляются из базы) ───────────
  function attachMessageId(rowEl, id) {
    if (!rowEl || id == null) return;
    const key = String(id);
    rowEl.dataset.mid = key;
    state.msgEls.set(key, rowEl);
    const wrap = rowEl.querySelector('.bubble-wrap');
    if (wrap) addDeleteButton(wrap, key);
  }

  function addDeleteButton(wrapEl, id) {
    if (!wrapEl || wrapEl.querySelector('.msg-del')) return;
    const btn = el('button', 'msg-del', '×');
    btn.type = 'button';
    btn.setAttribute('aria-label', 'Удалить сообщение');
    btn.title = 'Удалить';
    let armed = false;
    let timer = null;
    btn.addEventListener('click', (e) => {
      e.preventDefault();
      e.stopPropagation();
      if (!armed) {
        armed = true;
        btn.classList.add('armed');
        btn.textContent = 'Удалить?';
        timer = setTimeout(() => {
          armed = false;
          btn.classList.remove('armed');
          btn.textContent = '×';
        }, 2800);
        return;
      }
      clearTimeout(timer);
      btn.disabled = true;
      btn.textContent = '…';
      deleteMessageById(id);
    });
    wrapEl.appendChild(btn);
  }

  async function deleteMessageById(id) {
    if (!sb) return;
    try {
      const { error } = await sb.from('potok_messages').delete().eq('id', Number(id));
      if (error) throw error;
      removeMessageLocal(id);
    } catch (e) {
      toast('Не удалось удалить сообщение');
      const node = state.msgEls.get(String(id));
      const btn = node && node.querySelector('.msg-del');
      if (btn) { btn.disabled = false; btn.classList.remove('armed'); btn.textContent = '×'; }
    }
  }

  function removeMessageLocal(id) {
    const key = String(id);
    const node = state.msgEls.get(key);
    if (node) {
      state.msgEls.delete(key);
      if (node.isConnected) { node.remove(); state.msgCount--; }
    }
    state.seen.delete(key);
    removeFromCache(key);
    if (state.msgCount <= 0) maybeShowEmpty();
  }

  function removeFromCache(id) {
    try {
      const arr = loadCache();
      const filtered = arr.filter((m) => String(m.id) !== String(id));
      if (filtered.length !== arr.length) safeSet(cacheKey(), JSON.stringify(filtered));
    } catch (e) {}
  }

  // ── Доступ: сессия → членство → код ─────────────────────────
  function accessFail(text) {
    setConn('error');
    showBanner(text);
  }

  function setGateBusy(busy, label) {
    if (!passSubmit) return;
    passSubmit.disabled = busy;
    passSubmit.textContent = busy ? label : 'Войти';
  }

  async function ensureSession() {
    if (!sb) throw new Error('no-supabase-client');
    const cur = await sb.auth.getSession();
    if (cur && cur.data && cur.data.session) { currentUser = cur.data.session.user; return; }
    const anon = await sb.auth.signInAnonymously();
    if (anon.error) throw anon.error;
    currentUser = (anon.data && anon.data.user) || null;
  }

  let sessionPromise = null;
  function ensureSessionOnce() {
    if (!sessionPromise) {
      sessionPromise = ensureSession().catch((e) => { sessionPromise = null; throw e; });
    }
    return sessionPromise;
  }

  async function checkMember() {
    const r = await sb.rpc('potok_is_member');
    if (r.error) throw r.error;
    return r.data === true;
  }

  async function tryJoin(code) {
    const r = await sb.rpc('potok_join', { p_code: code });
    if (r.error) throw r.error;
    return r.data === true;
  }

  const BLOCKED_HINT = 'Похоже, эта площадка блокирует подключения базе. Откройте рабочую версию: konovalius.github.io/potok';
  function blockedHintNeeded() { return /autoclawai\.space$/i.test(location.hostname); }

  async function startAccess() {
    setConn('connecting');
    setGateBusy(false);
    clearTimeout(slowTimer);
    slowTimer = setTimeout(() => { if (!state.joined) slowNote.hidden = false; }, 9000);
    if (!sb) { clearTimeout(slowTimer); accessFail('Не удалось загрузить клиент базы — обновите страницу.'); return; }
    try {
      await ensureSessionOnce();
    } catch (e) {
      clearTimeout(slowTimer);
      accessFail(blockedHintNeeded() ? BLOCKED_HINT : 'Нет связи с базой — проверьте интернет и нажмите «Переподключиться».');
      return;
    }
    let member = false;
    try { member = await checkMember(); } catch (e) { member = false; }
    clearTimeout(slowTimer);
    if (member) {
      const keyOk = await loadStoredKey();
      if (keyOk) enterChat();
      else showPassGate();
    } else {
      showPassGate();
    }
  }

  function showPassGate() {
    document.documentElement.classList.remove('has-session');
    passGate.hidden = false;
    setConn('connecting');
    setTimeout(() => passInput.focus(), 80);
  }

  function enterChat() {
    state.joined = true;
    clearTimeout(slowTimer);
    removeSkeleton();
    document.documentElement.classList.add('has-session');
    passGate.hidden = true;
    hideBanner();
    ensureAudio();
    if (!state.name) {
      applyName(defaultGuestName());
      addNote('Вы в чате как «' + state.name + '» — имя можно поменять в настройках');
    }
    if (state.msgCount === 0) maybeShowEmpty();
    loadRoom();
    initWall();
    setTimeout(() => composerInput.focus(), 120);
  }

  passForm.addEventListener('submit', async (e) => {
    e.preventDefault();
    const v = passInput.value.trim();
    if (!v) { showFieldError(passInput, passError, 'Введите код доступа.'); passInput.focus(); return; }
    clearFieldError(passInput, passError);
    setGateBusy(true, 'Проверяем…');
    try {
      await ensureSessionOnce(); // на случай, если сессия ещё не успела создаться
      const ok = await tryJoin(v);
      if (ok) {
        hideBanner();
        try { await setUpKey(v); } catch (e) { toast('Не удалось включить шифрование — проверьте браузер.'); }
        document.documentElement.classList.add('has-session');
        enterChat();
      } else {
        showFieldError(passInput, passError, 'Неверный код — попробуйте ещё раз.');
        passInput.select();
      }
    } catch (err) {
      showFieldError(passInput, passError, (err && err.code === '42501')
        ? 'Секунду — сессия ещё создаётся. Попробуйте ещё раз.'
        : (blockedHintNeeded() ? 'Площадка блокирует соединения — откройте рабочую версию.' : 'Нет связи с базой — проверьте интернет.'));
    } finally {
      setGateBusy(false);
    }
  });
  passInput.addEventListener('input', () => { if (!passError.hidden) clearFieldError(passInput, passError); });

  // ── Комнаты: загрузка из базы и realtime ────────────────────
  async function rowToMessage(row, quiet) {
    const id = String(row.id);
    if (state.seen.has(id)) return;
    const cmid = row.client_msg_id;
    if (cmid && state.pending.has(cmid)) {
      // эхо собственного сообщения — финализируем оптимистичный пузырь (текст уже есть)
      const p = state.pending.get(cmid);
      p.reconciled = true;
      state.pending.delete(cmid);
      state.seen.add(id);
      if (p.el.isConnected) {
        p.el.classList.remove('msg-pending', 'msg-error');
        if (p.st && p.st.isConnected) p.st.remove();
      }
      attachMessageId(p.el, id);
      addToCache({ id, n: state.name, t: p.time, x: p.text, u: row.user_id || (currentUser && currentUser.id) || null });
      return;
    }
    const time = row.created_at ? Date.parse(row.created_at) : Date.now();
    const dec = await decryptPayload(row.body || '');
    const name = dec.plain ? (((typeof row.author === 'string' && row.author.trim()) || 'Гость')) : (dec.n || '·');
    const mine = isMine(row.user_id, name);
    renderMessage({ name, text: dec.t, time, mine, noAnim: !!quiet, id, userId: row.user_id || null, locked: dec.failed });
    state.seen.add(id);
    addToCache({ id, n: name, t: time, x: dec.t, u: row.user_id || null });
    if (quiet) return;
    const age = Date.now() - time;
    if (!mine && !dec.failed && age < LIVE_WINDOW) {
      blip();
      if (document.hidden || !isNearBottom()) state.unread++;
      updateUnreadUI();
    }
  }

  function unsubscribeChannel() {
    if (channel) { try { sb.removeChannel(channel); } catch (e) {} channel = null; }
  }

  function subscribeRoom() {
    unsubscribeChannel();
    if (!sb || !state.joined) return;
    channel = sb.channel('potok-' + slugifyRoom(state.room));
    channel
      .on('postgres_changes', { event: 'INSERT', schema: 'public', table: 'potok_messages' }, async (payload) => {
        const row = payload && payload.new;
        if (!row) return;
        if (row.room !== state.room) {
          // личное сообщение, пришедшее, пока мы в другом чате
          const dec = await decryptPayload(row.body || '');
          const nm = dec.plain ? (((row.author || '').trim()) || 'Гость') : (dec.n || 'Гость');
          if (isDmForMe(row.room) && !isMine(row.user_id, nm)) {
            blip();
            toast('Личное сообщение от «' + nm + '»', () => openDM(row.user_id, nm));
          }
          return;
        }
        await rowToMessage(row, false);
      })
      .on('postgres_changes', { event: 'DELETE', schema: 'public', table: 'potok_messages' }, (payload) => {
        const oldRow = payload && payload.old;
        if (!oldRow || oldRow.id == null) return;
        removeMessageLocal(String(oldRow.id));
      })
      .subscribe((status) => {
        if (status === 'SUBSCRIBED') { setConn('online'); hideBanner(); }
        else if (status === 'CHANNEL_ERROR' || status === 'TIMED_OUT') { setConn('reconnecting'); }
      });
  }

  async function loadRoom() {
    if (!sb || !state.joined) return;
    const roomToken = state.room;
    setConn('connecting');
    try {
      const { data, error } = await sb
        .from('potok_messages')
        .select('id, room, author, body, client_msg_id, user_id, created_at')
        .eq('room', state.room)
        .order('created_at', { ascending: false })
        .limit(HISTORY_LIMIT);
      if (error) throw error;
      if (state.room !== roomToken) return;
      const rows = (data || []).slice().reverse();
      let count = 0;
      for (const row of rows) {
        const before = state.msgCount;
        await rowToMessage(row, true);
        if (state.msgCount > before) count++;
      }
      removeSkeleton();
      if (state.msgCount === 0) maybeShowEmpty(); else hideEmpty();
      if (count) requestAnimationFrame(() => scrollToBottom('auto'));
      clearTimeout(loadTimer);
      hideBanner();
      subscribeRoom();
    } catch (e) {
      if (state.room !== roomToken) return;
      setConn('error');
      showBanner('Нет связи с базой — проверьте интернет. Пробуем ещё раз…');
      clearTimeout(loadTimer);
      loadTimer = setTimeout(() => { if (state.joined && state.room === roomToken) loadRoom(); }, 6000);
    }
  }

  // ── Отправка ────────────────────────────────────────────────
  async function publish(cmid) {
    const p = state.pending.get(cmid);
    if (!p) return;
    if (!cryptoKey) {
      p.failed = true;
      if (p.el.isConnected) { p.el.classList.add('msg-error'); p.el.classList.remove('msg-pending'); }
      setStatusNode(p, 'failed');
      toast('Нет ключа шифрования — войдите по коду заново.');
      showPassGate();
      return;
    }
    try {
      const encBody = await encryptPayload({ t: p.text, n: state.name });
      const { data, error } = await sb
        .from('potok_messages')
        .insert({ room: state.room, author: '•', body: encBody, client_msg_id: cmid })
        .select('id, author, created_at, client_msg_id')
        .single();
      if (error) {
        if (error.code === '23505') { // повторная вставка после сбоя — уже доставлено
          state.pending.delete(cmid);
          if (p.el.isConnected) { p.el.classList.remove('msg-pending'); if (p.st && p.st.isConnected) p.st.remove(); }
          return;
        }
        throw error;
      }
      const id = String(data.id);
      if (p.reconciled) return; // realtime уже финализировал этот пузырь
      state.pending.delete(cmid);
      if (state.seen.has(id)) {
        if (p.el.isConnected) { p.el.remove(); state.msgCount--; }
      } else {
        state.seen.add(id);
        if (p.el.isConnected) { p.el.classList.remove('msg-pending'); if (p.st && p.st.isConnected) p.st.remove(); }
        attachMessageId(p.el, id);
        addToCache({ id, n: state.name, t: p.time, x: p.text, u: (currentUser && currentUser.id) || null });
      }
    } catch (err) {
      p.failed = true;
      if (p.el.isConnected) { p.el.classList.add('msg-error'); p.el.classList.remove('msg-pending'); }
      setStatusNode(p, 'failed');
      toast('Сообщение не отправилось. Нажмите «повторить» под ним.');
    }
  }

  function retryMessage(cmid) {
    const p = state.pending.get(cmid);
    if (!p) return;
    p.failed = false;
    if (p.el.isConnected) { p.el.classList.remove('msg-error'); p.el.classList.add('msg-pending'); }
    setStatusNode(p, 'pending');
    publish(cmid);
  }

  function sendText(text) {
    if (!state.joined) { toast('Сначала войдите в чат по коду доступа.'); showPassGate(); return; }
    if (!state.name) applyName(defaultGuestName());
    const t0 = Date.now();
    const cmid = (window.crypto && crypto.randomUUID) ? crypto.randomUUID() : (t0 + '-' + Math.random().toString(16).slice(2));
    const built = renderMessage({ name: state.name, text, time: t0, mine: true, pending: true });
    const p = { id: cmid, el: built.row, st: built.st, text, time: t0, failed: false, reconciled: false };
    state.pending.set(cmid, p);
    publish(cmid);
  }

  // ── Композер ────────────────────────────────────────────────
  function autosize() {
    composerInput.style.height = 'auto';
    composerInput.style.height = Math.min(composerInput.scrollHeight, 132) + 'px';
  }
  function updateSendState() {
    sendBtn.disabled = composerInput.value.trim().length === 0;
  }
  function updateCounter() {
    const len = composerInput.value.length;
    const left = MAX_TEXT - len;
    if (left <= 120) {
      charCounter.hidden = false;
      charCounter.textContent = 'осталось ' + Math.max(left, 0);
      charCounter.classList.toggle('warn', left <= 40);
    } else {
      charCounter.hidden = true;
      charCounter.classList.remove('warn');
    }
  }
  function sendFromComposer() {
    const text = composerInput.value.trim();
    if (!text || text.length > MAX_TEXT) return;
    composerInput.value = '';
    autosize();
    updateSendState();
    updateCounter();
    if (state.unread > 0) { state.unread = 0; updateUnreadUI(); }
    sendText(text);
  }
  composerForm.addEventListener('submit', (e) => { e.preventDefault(); sendFromComposer(); });
  composerInput.addEventListener('input', () => { autosize(); updateSendState(); updateCounter(); });
  composerInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' && !e.shiftKey && !e.isComposing) {
      e.preventDefault();
      sendFromComposer();
    }
  });

  // ── Имя и модалки ───────────────────────────────────────────
  function validateName(v) {
    if (v.length < 2) return 'Введите имя — хотя бы 2 символа.';
    if (v.length > 24) return 'Слишком длинное имя — максимум 24 символа.';
    return '';
  }
  function showFieldError(input, errNode, msg) {
    input.classList.add('is-invalid');
    input.setAttribute('aria-invalid', 'true');
    errNode.textContent = msg;
    errNode.hidden = false;
  }
  function clearFieldError(input, errNode) {
    input.classList.remove('is-invalid');
    input.removeAttribute('aria-invalid');
    errNode.hidden = true;
    errNode.textContent = '';
  }

  function applyName(name) {
    state.name = name;
    safeSet(LS.name, name);
    safeSSet('potok.v1.name_tab', name);
    meName.textContent = name;
    paintAvatar(meAvatar, name);
  }
  function openSettings() {
    settingsName.value = state.name;
    soundToggle.checked = state.sound;
    clearFieldError(settingsName, settingsNameError);
    settings.hidden = false;
    setTimeout(() => settingsName.focus(), 80);
  }
  function closeSettings() {
    settings.hidden = true;
    meBtn.focus();
  }
  meBtn.addEventListener('click', () => openSettings());
  backBtn.addEventListener('click', goGeneral);
  settingsClose.addEventListener('click', closeSettings);
  settings.addEventListener('click', (e) => { if (e.target === settings) closeSettings(); });

  settingsForm.addEventListener('submit', (e) => {
    e.preventDefault();
    const v = settingsName.value.trim();
    const err = validateName(v);
    if (err) { showFieldError(settingsName, settingsNameError, err); settingsName.focus(); return; }
    clearFieldError(settingsName, settingsNameError);

    const nameChanged = v !== state.name;
    if (nameChanged) {
      applyName(v);
      addNote('Теперь вы пишете как «' + v + '»');
    }
    state.sound = soundToggle.checked;
    safeSet(LS.sound, state.sound ? '1' : '0');
    if (state.sound) ensureAudio();

    closeSettings();
    toast('Сохранено');
  });
  settingsName.addEventListener('input', () => {
    if (!settingsNameError.hidden) {
      const err = validateName(settingsName.value.trim());
      if (!err) clearFieldError(settingsName, settingsNameError);
    }
  });
  soundToggle.addEventListener('change', () => {
    if (soundToggle.checked) ensureAudio();
  });

  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && !settings.hidden) closeSettings();
  });

  // ── Чаты: общий и личные ───────────────────────────────────
  function dmKeyFor(otherId) {
    const a = (currentUser && currentUser.id) || '';
    const b = String(otherId);
    const pair = [a, b].sort();
    return 'dm:' + pair[0] + ':' + pair[1];
  }
  function isDmForMe(roomKey) {
    if (!roomKey || roomKey.indexOf('dm:') !== 0 || !currentUser) return false;
    const parts = roomKey.split(':');
    return parts[1] === currentUser.id || parts[2] === currentUser.id;
  }

  function syncRoomUI() {
    const inDm = !!state.dmPeer;
    roomHashEl.textContent = inDm ? '@' : '#';
    roomLabelEl.textContent = inDm ? state.dmPeer.name : DEFAULT_ROOM;
    backBtn.hidden = !inDm;
    composerInput.placeholder = inDm ? ('Личное сообщение для «' + state.dmPeer.name + '»') : ('Сообщение в #' + DEFAULT_ROOM);
    state.baseTitle = inDm ? ('Поток — личный чат с «' + state.dmPeer.name + '»') : 'Поток — общий чат';
    emptyTitle.textContent = inDm ? 'Личный чат' : 'Здесь пока тихо';
    emptyTextEl.textContent = inDm
      ? ('Сообщения здесь видят только вы и «' + state.dmPeer.name + '».')
      : 'Напишите первое сообщение — его увидят все, кто в общем чате. Сообщения появляются сверху вниз, у всех сразу.';
    updateUnreadUI();
  }

  function switchRoom(roomKey) {
    state.room = roomKey;
    chatList.textContent = '';
    state.seen.clear();
    state.pending.clear();
    state.msgCount = 0;
    state.lastDay = '';
    state.lastAuthor = '';
    state.lastTime = 0;
    state.unread = 0;
    jumpBtn.hidden = true;
    skeleton.hidden = false;
    slowNote.hidden = true;
    emptyState.hidden = true;
    syncRoomUI();
    renderCached();
    addNote(state.dmPeer ? ('Личный чат с «' + state.dmPeer.name + '»') : 'Общий чат');
    unsubscribeChannel();
    if (state.joined) loadRoom();
  }

  function openDM(peerId, peerName) {
    if (!state.joined || !currentUser || !peerId || peerId === currentUser.id) return;
    state.dmPeer = { id: String(peerId), name: ((peerName || '').trim() || 'Гость') };
    switchRoom(dmKeyFor(peerId));
  }

  function goGeneral() {
    if (!state.dmPeer && state.room === DEFAULT_ROOM) return;
    state.dmPeer = null;
    switchRoom(DEFAULT_ROOM);
  }

  function addNote(text) {
    const n = el('div', 'note', text);
    chatList.appendChild(n);
  }

  // ── Стена: общий холст для рисования ───────────────────────
  const WALL_ROOM = 'wall';
  const WALL_FONTS = {
    sans: "'Segoe UI', system-ui, sans-serif",
    hand: "'Segoe Script', 'Comic Sans MS', cursive",
    poster: "Impact, 'Arial Black', sans-serif",
    mono: "'Courier New', monospace",
    serif: "Georgia, 'Times New Roman', serif"
  };
  const WALL_COLORS = { ink: '#1a1916', terra: '#c96442', blue: '#3b6ea5', green: '#4a8c5c', yellow: '#e0a63a', pink: '#c65b8a' };
  const wallState = {
    ready: false,
    loaded: false,
    strokes: [],
    byId: new Map(),
    byDb: new Map(),
    live: new Map(),
    drawing: null,
    tool: 'brush',
    color: '#1a1916',
    size: 6,
    opacity: 1,
    collapsed: false,
    renderScheduled: false
  };
  let wallChannel = null;
  let wallLastSend = 0;
  let wallPendingPts = [];
  let wallClearArmed = false;
  let wallClearTimer = null;

  const wallEl = $('wall');
  const wallCanvas = $('wallCanvas');
  const wallPreview = $('wallPreview');
  const wallToggleBtn = $('wallToggle');
  const wallUndoBtn = $('wallUndo');
  const wallSaveBtn = $('wallSave');
  const wallClearBtn = $('wallClear');
  const wallToolsEl = $('wallTools');
  const wallColorsEl = $('wallColors');
  const wallSizesEl = $('wallSizes');
  const wallOpacityEl = $('wallOpacity');
  const wallCollapsedNote = $('wallCollapsedNote');
  const wallCustom = $('wallCustom');
  const wallTextRow = $('wallTextRow');
  const wallTextInput = $('wallTextInput');
  const wallFontSel = $('wallFont');
  const wallCtx = wallCanvas ? wallCanvas.getContext('2d') : null;
  const wallPreviewCtx = wallPreview ? wallPreview.getContext('2d') : null;

  function sidSeed(sid) {
    let h = 0;
    for (let i = 0; i < sid.length; i++) h = (h * 31 + sid.charCodeAt(i)) | 0;
    return h;
  }
  function mulberry32(a) {
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function drawWallStroke(ctx, s, w, h) {
    if (!s || !ctx) return;
    const lw = Math.max((s.w || 0.006) * w, 0.6);
    const erase = s.m === 'erase';
    ctx.save();
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    ctx.strokeStyle = s.c || '#1a1916';
    ctx.fillStyle = s.c || '#1a1916';
    ctx.lineWidth = lw;
    const baseAlpha = (s.o != null && s.o !== '') ? Math.min(1, Math.max(0.05, Number(s.o) || 1)) : 1;
    if (erase) ctx.globalCompositeOperation = 'destination-out';
    else ctx.globalAlpha = baseAlpha;
    if (s.t === 'brush' || s.t === 'marker' || s.t === 'eraser') {
      const pts = s.pts || [];
      if (!pts.length) { ctx.restore(); return; }
      if (pts.length === 1) {
        ctx.beginPath();
        ctx.arc(pts[0][0] * w, pts[0][1] * h, lw / 2, 0, Math.PI * 2);
        ctx.fill();
      } else {
        ctx.beginPath();
        ctx.moveTo(pts[0][0] * w, pts[0][1] * h);
        for (let i = 1; i < pts.length - 1; i++) {
          const xc = (pts[i][0] + pts[i + 1][0]) / 2 * w;
          const yc = (pts[i][1] + pts[i + 1][1]) / 2 * h;
          ctx.quadraticCurveTo(pts[i][0] * w, pts[i][1] * h, xc, yc);
        }
        ctx.lineTo(pts[pts.length - 1][0] * w, pts[pts.length - 1][1] * h);
        ctx.stroke();
      }
    } else if (s.t === 'spray') {
      const pts = s.pts || [];
      const rad = Math.max(lw * 2.4, 7);
      for (let i = 0; i < pts.length; i++) {
        const idx = (s.__idx != null ? s.__idx : 0) + i;
        const rnd = mulberry32((sidSeed(s.s) ^ Math.imul(idx + 1, 0x9E3779B1)) | 0);
        const x = pts[i][0] * w;
        const y = pts[i][1] * h;
        for (let k = 0; k < 10; k++) {
          const ang = rnd() * Math.PI * 2;
          const rr = rnd() * rad;
          const d = 0.9 + rnd() * 1.3;
          ctx.globalAlpha = (0.05 + rnd() * 0.08) * baseAlpha;
          ctx.beginPath();
          ctx.arc(x + Math.cos(ang) * rr, y + Math.sin(ang) * rr, d, 0, Math.PI * 2);
          ctx.fill();
        }
      }
      ctx.globalAlpha = 1;
    } else if (s.t === 'line' && s.p1 && s.p2) {
      ctx.beginPath();
      ctx.moveTo(s.p1[0] * w, s.p1[1] * h);
      ctx.lineTo(s.p2[0] * w, s.p2[1] * h);
      ctx.stroke();
    } else if (s.t === 'rect' && s.p1 && s.p2) {
      ctx.strokeRect(Math.min(s.p1[0], s.p2[0]) * w, Math.min(s.p1[1], s.p2[1]) * h, Math.abs(s.p2[0] - s.p1[0]) * w, Math.abs(s.p2[1] - s.p1[1]) * h);
    } else if (s.t === 'ellipse' && s.p1 && s.p2) {
      ctx.beginPath();
      ctx.ellipse(((s.p1[0] + s.p2[0]) / 2) * w, ((s.p1[1] + s.p2[1]) / 2) * h, Math.abs(s.p2[0] - s.p1[0]) / 2 * w, Math.abs(s.p2[1] - s.p1[1]) / 2 * h, 0, 0, Math.PI * 2);
      ctx.stroke();
    } else if (s.t === 'text' && s.p && s.tx) {
      ctx.font = Math.max((s.w || 0.02) * w, 10) + 'px ' + (WALL_FONTS[s.f] || WALL_FONTS.sans);
      ctx.textBaseline = 'top';
      ctx.fillText(String(s.tx).slice(0, 40), s.p[0] * w, s.p[1] * h);
    }
    ctx.restore();
  }

  function wallFullRender() {
    if (!wallCanvas || !wallCtx) return;
    const w = wallCanvas.clientWidth;
    const h = wallCanvas.clientHeight;
    if (!w || !h) return;
    const dpr = window.devicePixelRatio || 1;
    if (wallCanvas.width !== Math.round(w * dpr)) { wallCanvas.width = Math.round(w * dpr); wallCanvas.height = Math.round(h * dpr); }
    if (wallPreview.width !== wallCanvas.width) { wallPreview.width = wallCanvas.width; wallPreview.height = wallCanvas.height; }
    wallCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
    if (wallPreviewCtx) wallPreviewCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
    wallCtx.clearRect(0, 0, w, h);
    const ordered = wallState.strokes.slice().sort((a, b) => (a.tm - b.tm) || 0);
    for (const s of ordered) drawWallStroke(wallCtx, s, w, h);
    for (const s of wallState.live.values()) drawWallStroke(wallCtx, s, w, h);
    if (wallState.drawing) drawWallStroke(wallCtx, wallState.drawing, w, h);
  }
  function scheduleWallRender() {
    if (wallState.renderScheduled) return;
    wallState.renderScheduled = true;
    requestAnimationFrame(() => { wallState.renderScheduled = false; wallFullRender(); });
  }
  function wallPreviewClear() {
    if (!wallPreview || !wallPreviewCtx) return;
    wallPreviewCtx.save();
    wallPreviewCtx.setTransform(1, 0, 0, 1, 0, 0);
    wallPreviewCtx.clearRect(0, 0, wallPreview.width, wallPreview.height);
    wallPreviewCtx.restore();
  }

  function wallPos(e) {
    const r = wallCanvas.getBoundingClientRect();
    return [Math.min(1, Math.max(0, (e.clientX - r.left) / r.width)), Math.min(1, Math.max(0, (e.clientY - r.top) / r.height))];
  }

  function wallBroadcastChunk(s, pts, first) {
    if (!wallChannel) return;
    const obj = first ? { s: s.s, t: s.t, c: s.c, w: s.w, m: s.m, o: s.o, a: pts } : { s: s.s, a: pts };
    encryptPayload(obj).then((enc) => {
      try { wallChannel.send({ type: 'broadcast', event: 'draw', payload: { e: enc } }); } catch (e) {}
    }).catch(() => {});
  }

  function wallPointerDown(e) {
    if (!wallState.ready || !state.joined || !cryptoKey) return;
    if (e.isPrimary === false) return;
    e.preventDefault();
    const tool = wallState.tool;
    const [x, y] = wallPos(e);
    if (tool === 'text') {
      const tx = (wallTextInput.value || '').trim();
      if (!tx) { toast('Введите текст для надписи'); wallTextInput.focus(); return; }
      commitWallStroke({ t: 'text', c: wallState.color, o: wallState.opacity, w: wallState.size / Math.max(wallCanvas.clientWidth, 1), p: [x, y], tx, f: wallFontSel.value || 'sans' });
      return;
    }
    try { wallCanvas.setPointerCapture(e.pointerId); } catch (err) {}
    const base = {
      s: (window.crypto && crypto.randomUUID) ? crypto.randomUUID() : 's' + Date.now() + Math.random().toString(16).slice(2),
      t: tool,
      c: wallState.color,
      o: wallState.opacity,
      w: wallState.size / Math.max(wallCanvas.clientWidth, 1)
    };
    if (tool === 'brush' || tool === 'marker' || tool === 'spray' || tool === 'eraser') {
      base.m = tool === 'eraser' ? 'erase' : 'ink';
      base.pts = [[x, y]];
      wallState.drawing = base;
      wallPendingPts = [[x, y]];
      wallBroadcastChunk(base, [[x, y]], true);
      drawWallStroke(wallCtx, base, wallCanvas.clientWidth, wallCanvas.clientHeight);
    } else {
      base.p1 = [x, y];
      base.p2 = [x, y];
      wallState.drawing = base;
      wallPreviewClear();
      drawWallStroke(wallPreviewCtx, base, wallPreview.clientWidth, wallPreview.clientHeight);
    }
  }

  function wallPointerMove(e) {
    const s = wallState.drawing;
    if (!s) return;
    if (e.isPrimary === false) return;
    const [x, y] = wallPos(e);
    if (s.pts) {
      const last = s.pts[s.pts.length - 1];
      if (Math.abs(x - last[0]) < 0.0018 && Math.abs(y - last[1]) < 0.0018) return;
      s.pts.push([x, y]);
      wallPendingPts.push([x, y]);
      if (s.t === 'spray') {
        drawWallStroke(wallCtx, { s: s.s, t: 'spray', c: s.c, w: s.w, m: s.m, o: s.o, pts: [[x, y]], __idx: s.pts.length - 1 }, wallCanvas.clientWidth, wallCanvas.clientHeight);
      } else {
        drawWallStroke(wallCtx, { s: s.s, t: s.t, c: s.c, w: s.w, m: s.m, o: s.o, pts: [last, [x, y]] }, wallCanvas.clientWidth, wallCanvas.clientHeight);
      }
      const now = Date.now();
      if (now - wallLastSend > 45 && wallPendingPts.length) {
        wallLastSend = now;
        const chunk = wallPendingPts;
        wallPendingPts = [];
        wallBroadcastChunk(s, chunk, false);
      }
    } else {
      s.p2 = [x, y];
      wallPreviewClear();
      drawWallStroke(wallPreviewCtx, s, wallPreview.clientWidth, wallPreview.clientHeight);
    }
  }

  function wallPointerUp() {
    const s = wallState.drawing;
    if (!s) return;
    wallState.drawing = null;
    wallPreviewClear();
    if (s.pts) {
      if (wallPendingPts.length) { wallBroadcastChunk(s, wallPendingPts, false); wallPendingPts = []; }
      if (s.pts.length < 2) s.pts.push([s.pts[0][0] + 0.0006, s.pts[0][1] + 0.0006]);
    }
    commitWallStroke(s);
  }
  function commitWallStroke(s) {
    s.tm = Date.now();
    s.uid = (currentUser && currentUser.id) || null;
    wallState.strokes.push(s);
    wallState.byId.set(s.s, s);
    scheduleWallRender();
    setTimeout(scheduleWallRender, 450);
    persistWallStroke(s);
  }

  async function persistWallStroke(s) {
    try {
      const payload = await encryptPayload({ s: s.s, t: s.t, c: s.c, w: s.w, m: s.m, o: s.o, pts: s.pts, p1: s.p1, p2: s.p2, p: s.p, tx: s.tx, f: s.f });
      const { data, error } = await sb.from('potok_strokes').insert({ room: WALL_ROOM, payload }).select('id, created_at').single();
      if (error) throw error;
      s.dbId = data.id;
      wallState.byDb.set(String(data.id), s.s);
      if (data.created_at) s.tm = Date.parse(data.created_at);
    } catch (err) {
      toast('Штрих не сохранился — пропадёт после перезагрузки');
    }
  }

  function removeWallStroke(dbId) {
    const sid = wallState.byDb.get(String(dbId));
    if (!sid) return;
    wallState.byDb.delete(String(dbId));
    wallState.byId.delete(sid);
    const i = wallState.strokes.findIndex((x) => x.s === sid);
    if (i >= 0) wallState.strokes.splice(i, 1);
    wallState.live.delete(sid);
    scheduleWallRender();
  }

  let wallLastTs = 0;
  let wallPollTimer = null;
  let wallPollTicks = 0;

  async function ingestWallRow(row) {
    if (!row || !row.id) return false;
    const key = String(row.id);
    if (row.created_at) { const t = Date.parse(row.created_at); if (t > wallLastTs) wallLastTs = t; }
    if (wallState.byDb.has(key)) return false;
    const dec = await decryptPayload(row.payload || '');
    if (dec.failed || dec.plain) return false;
    let st = (dec.obj && typeof dec.obj === 'object') ? dec.obj : null;
    if (!st) return false;
    if (!st || !st.s) return false;
    const ex = wallState.byId.get(st.s);
    if (ex) {
      ex.dbId = row.id;
      wallState.byDb.set(key, st.s);
      if (ex.partial) {
        Object.assign(ex, st, { partial: false, dbId: row.id });
        if (row.created_at) ex.tm = Date.parse(row.created_at);
        return true;
      }
      return false;
    }
    st.tm = row.created_at ? Date.parse(row.created_at) : Date.now();
    st.dbId = row.id;
    st.uid = row.user_id || null;
    wallState.strokes.push(st);
    wallState.byId.set(st.s, st);
    wallState.byDb.set(key, st.s);
    wallState.live.delete(st.s);
    return true;
  }

  async function loadWallStrokes() {
    if (!sb || wallState.loaded) return;
    try {
      const { data, error } = await sb.from('potok_strokes')
        .select('id, room, payload, user_id, created_at')
        .eq('room', WALL_ROOM)
        .order('created_at', { ascending: true })
        .limit(2000);
      if (error) throw error;
      for (const row of (data || [])) { await ingestWallRow(row); }
      wallState.loaded = true;
      scheduleWallRender();
    } catch (e) { /* стена догрузится позже */ }
  }

  function withTimeout(promise, ms) {
    return Promise.race([
      promise,
      new Promise((resolve) => setTimeout(() => resolve({ timeout: true }), ms))
    ]);
  }

  async function pollWallAdds() {
    if (!sb || !state.joined || !wallState.ready) return;
    try {
      const sinceIso = new Date(Math.max(wallLastTs - 1000, 0)).toISOString();
      const res = await withTimeout(sb.from('potok_strokes')
        .select('id, room, payload, user_id, created_at')
        .eq('room', WALL_ROOM)
        .gt('created_at', sinceIso)
        .order('created_at', { ascending: true })
        .limit(100), 45000);
      if (!res || res.timeout) { wallState.pollErr = 'timeout'; return; }
      const { data, error } = res;
      if (error) { wallState.pollErr = String(error.message || 'poll-error'); return; }
      let changed = false;
      for (const row of (data || [])) { if (await ingestWallRow(row)) changed = true; }
      if (changed) scheduleWallRender();
    } catch (e) { wallState.pollErr = String((e && e.message) || 'poll-exc'); }
  }

  async function pollWallReconcile() {
    if (!sb || !state.joined || !wallState.ready) return;
    try {
      const { data, error } = await sb.from('potok_strokes').select('id').eq('room', WALL_ROOM).limit(2000);
      if (error || !Array.isArray(data)) { if (error) wallState.pollErr = 'reconcile: ' + String(error.message || ''); return; }
      const ids = new Set(data.map((r) => String(r.id)));
      let changed = false;
      for (const s of wallState.strokes.slice()) {
        if (s.dbId && !ids.has(String(s.dbId))) {
          wallState.byId.delete(s.s);
          wallState.byDb.delete(String(s.dbId));
          const i = wallState.strokes.indexOf(s);
          if (i >= 0) wallState.strokes.splice(i, 1);
          changed = true;
        }
      }
      if (changed) scheduleWallRender();
    } catch (e) {}
  }

  function startWallPolling() {
    if (wallPollTimer) return;
    let tick = 0;
    const loop = async () => {
      tick++;
      wallPollTicks = tick;
      await pollWallAdds();
      if (tick % 5 === 0) await pollWallReconcile();
      wallPollTimer = setTimeout(loop, 6000);
    };
    wallPollTimer = setTimeout(loop, 5000);
    document.addEventListener('visibilitychange', () => { if (!document.hidden) pollWallAdds(); });
  }

  function initWall() {
    if (!wallEl || !wallCanvas) return;
    if (wallState.ready) { scheduleWallRender(); return; }
    wallState.ready = true;
    scheduleWallRender();
    loadWallStrokes();
    startWallPolling();
    if (!sb || !state.joined) return;
    try {
      wallChannel = sb.channel('potok-wall', { config: { broadcast: { self: false } } });
      wallChannel
        .on('postgres_changes', { event: 'INSERT', schema: 'public', table: 'potok_strokes' }, async (payload) => {
          const row = payload && payload.new;
          if (!row || row.room !== WALL_ROOM) return;
          if (await ingestWallRow(row)) scheduleWallRender();
        })
        .on('postgres_changes', { event: 'DELETE', schema: 'public', table: 'potok_strokes' }, (payload) => {
          const oldRow = payload && payload.old;
          if (!oldRow || oldRow.id == null) return;
          removeWallStroke(String(oldRow.id));
        })
        .on('broadcast', { event: 'draw' }, async (msg) => {
          const enc = msg && msg.payload && msg.payload.e;
          if (!enc) return;
          const dec = await decryptPayload(enc);
          if (dec.failed || dec.plain) return;
          chunk = (dec.obj && typeof dec.obj === 'object') ? dec.obj : null;
          if (!chunk) return;
          if (!chunk || !chunk.s || wallState.byId.has(chunk.s)) return;
          let live = wallState.live.get(chunk.s);
          if (!live) {
            live = { s: chunk.s, t: chunk.t || 'brush', c: chunk.c || '#1a1916', w: chunk.w || 0.008, m: chunk.m || 'ink', o: chunk.o, pts: [], partial: true, tm: Date.now() };
            wallState.live.set(chunk.s, live);
          }
          if (Array.isArray(chunk.a) && chunk.a.length) live.pts = live.pts.concat(chunk.a);
          scheduleWallRender();
        })
        .subscribe(() => {});
    } catch (e) { wallChannel = null; }
  }

  function setWallTool(tool) {
    wallState.tool = tool;
    wallToolsEl.querySelectorAll('.wbtn').forEach((b) => b.classList.toggle('active', b.dataset.tool === tool));
    wallTextRow.hidden = tool !== 'text';
    if (tool === 'text') wallTextInput.focus();
  }
  function setWallColorKey(key, raw) {
    wallState.color = raw || WALL_COLORS[key] || '#1a1916';
    wallColorsEl.querySelectorAll('.wswatch').forEach((b) => b.classList.toggle('active', b.dataset.c === key));
  }
  function setWallOpacity(v) {
    wallState.opacity = v;
    wallOpacityEl.querySelectorAll('.wop').forEach((b) => b.classList.toggle('active', Number(b.dataset.o) === v));
  }

  wallToolsEl.addEventListener('click', (e) => {
    const btn = e.target.closest('.wbtn');
    if (btn && btn.dataset.tool) setWallTool(btn.dataset.tool);
  });
  wallColorsEl.addEventListener('click', (e) => {
    const b = e.target.closest('.wswatch');
    if (b) setWallColorKey(b.dataset.c);
  });
  wallCustom.addEventListener('input', () => {
    setWallColorKey(null, wallCustom.value);
    wallColorsEl.querySelectorAll('.wswatch').forEach((x) => x.classList.remove('active'));
  });
  wallSizesEl.addEventListener('click', (e) => {
    const b = e.target.closest('.wsize');
    if (!b) return;
    wallState.size = Number(b.dataset.size) || 6;
    wallSizesEl.querySelectorAll('.wsize').forEach((x) => x.classList.toggle('active', x === b));
  });
  wallOpacityEl.addEventListener('click', (e) => {
    const b = e.target.closest('.wop');
    if (!b) return;
    setWallOpacity(Number(b.dataset.o) || 1);
  });
  wallToggleBtn.addEventListener('click', () => {
    wallState.collapsed = !wallState.collapsed;
    wallEl.classList.toggle('collapsed', wallState.collapsed);
    if (wallCollapsedNote) wallCollapsedNote.hidden = !wallState.collapsed;
    const label = wallState.collapsed ? 'Развернуть стену' : 'Свернуть стену';
    wallToggleBtn.title = label;
    wallToggleBtn.setAttribute('aria-label', label);
    setTimeout(scheduleWallRender, 220);
  });
  wallUndoBtn.addEventListener('click', async () => {
    const mine = wallState.strokes.slice().reverse().find((s) => s.uid && currentUser && s.uid === currentUser.id);
    if (!mine) { toast('Нет ваших штрихов для отмены'); return; }
    if (!mine.dbId) { toast('Секунду — штрих ещё сохраняется'); return; }
    try {
      const { error } = await sb.from('potok_strokes').delete().eq('id', mine.dbId);
      if (error) throw error;
      removeWallStroke(String(mine.dbId));
    } catch (e) { toast('Не удалось отменить штрих'); }
  });
  wallSaveBtn.addEventListener('click', () => {
    try {
      const w = wallCanvas.clientWidth;
      const h = wallCanvas.clientHeight;
      const dpr = window.devicePixelRatio || 1;
      const off = document.createElement('canvas');
      off.width = w * dpr;
      off.height = h * dpr;
      const octx = off.getContext('2d');
      octx.scale(dpr, dpr);
      octx.fillStyle = '#fdfcfa';
      octx.fillRect(0, 0, w, h);
      const ordered = wallState.strokes.slice().sort((a, b) => (a.tm - b.tm) || 0);
      for (const s of ordered) drawWallStroke(octx, s, w, h);
      const a = document.createElement('a');
      a.download = 'potok-wall.png';
      a.href = off.toDataURL('image/png');
      a.click();
    } catch (e) { toast('Не удалось сохранить рисунок'); }
  });
  wallClearBtn.addEventListener('click', async () => {
    if (!wallClearArmed) {
      wallClearArmed = true;
      wallClearBtn.classList.add('armed');
      wallClearTimer = setTimeout(() => { wallClearArmed = false; wallClearBtn.classList.remove('armed'); }, 3000);
      return;
    }
    clearTimeout(wallClearTimer);
    wallClearArmed = false;
    wallClearBtn.classList.remove('armed');
    try {
      const { error } = await sb.from('potok_strokes').delete().eq('room', WALL_ROOM);
      if (error) throw error;
      wallState.strokes = [];
      wallState.byId.clear();
      wallState.byDb.clear();
      wallState.live.clear();
      scheduleWallRender();
    } catch (e) { toast('Не удалось очистить стену'); }
  });
  wallCanvas.addEventListener('pointerdown', wallPointerDown);
  wallCanvas.addEventListener('pointermove', wallPointerMove);
  wallCanvas.addEventListener('pointerup', wallPointerUp);
  wallCanvas.addEventListener('pointercancel', wallPointerUp);
  window.addEventListener('resize', () => scheduleWallRender());
  setWallTool('brush');
  wallColorsEl.querySelectorAll('.wswatch').forEach((b) => { b.style.background = WALL_COLORS[b.dataset.c] || '#1a1916'; });
  setWallColorKey('ink');
  setWallOpacity(1);
  wallCustom.value = WALL_COLORS.terra;
  wallSizesEl.querySelectorAll('.wsize').forEach((x) => x.classList.toggle('active', Number(x.dataset.size) === wallState.size));
  window.__wallDbg = () => ({
    ready: wallState.ready,
    loaded: wallState.loaded,
    opacity: wallState.opacity,
    collapsed: wallState.collapsed,
    strokes: wallState.strokes.length,
    byId: wallState.byId.size,
    byDb: wallState.byDb.size,
    lastTs: wallLastTs,
    ticks: wallPollTicks,
    pollErr: wallState.pollErr || '',
    hasKey: !!cryptoKey,
    joined: state.joined
  });

  // ── Приглашение ─────────────────────────────────────────────
  async function copyInvite() {
    const url = location.href.split('#')[0];
    let ok = false;
    try { await navigator.clipboard.writeText(url); ok = true; }
    catch (e) { ok = fallbackCopy(url); }
    toast(ok ? 'Ссылка на чат скопирована' : 'Скопируйте адрес из строки браузера');
  }
  function fallbackCopy(text) {
    const ta = el('textarea');
    ta.value = text;
    ta.style.position = 'fixed';
    ta.style.opacity = '0';
    document.body.appendChild(ta);
    ta.select();
    let ok = false;
    try { ok = document.execCommand('copy'); } catch (e) { ok = false; }
    ta.remove();
    return ok;
  }
  shareBtn.addEventListener('click', copyInvite);
  copyLinkBtn.addEventListener('click', copyInvite);
  retryBtn.addEventListener('click', () => { hideBanner(); startAccess(); });

  // Выход из приложения: закрываем сессию и возвращаемся к экрану кода
  let logoutArmed = false;
  let logoutTimer = null;
  logoutBtn.addEventListener('click', async () => {
    if (!logoutArmed) {
      logoutArmed = true;
      logoutBtn.classList.add('armed');
      logoutBtn.textContent = 'Точно выйти?';
      logoutTimer = setTimeout(() => {
        logoutArmed = false;
        logoutBtn.classList.remove('armed');
        logoutBtn.textContent = 'Выйти';
      }, 3000);
      return;
    }
    clearTimeout(logoutTimer);
    logoutBtn.disabled = true;
    logoutBtn.textContent = 'Выходим…';
    try { if (sb) await sb.auth.signOut(); } catch (e) {}
    try {
      const drop = [];
      for (let i = 0; i < localStorage.length; i++) {
        const k = localStorage.key(i);
        if (k && (k.indexOf(CACHE_PREFIX) === 0 || k === LS.key)) drop.push(k);
      }
      for (const k of drop) localStorage.removeItem(k);
      cryptoKey = null;
    } catch (e) {}
    location.reload();
  });

  // ── Кэш на старте ───────────────────────────────────────────
  function renderCached() {
    const items = loadCache();
    if (!items.length) return;
    let count = 0;
    for (const it of items) {
      if (!it || !it.id || state.seen.has(it.id)) continue;
      state.seen.add(it.id);
      const cachedMine = isMine(it.u || null, it.n || '');
      renderMessage({ name: it.n || 'Гость', text: it.x || '', time: it.t || Date.now(), mine: cachedMine, noAnim: true, id: it.id, userId: it.u || null });
      count++;
    }
    if (count) {
      removeSkeleton();
      requestAnimationFrame(() => scrollToBottom('auto'));
    }
  }

  // ── Старт ───────────────────────────────────────────────────
  function boot() {
    state.name = (safeSGet('potok.v1.name_tab') || safeGet(LS.name) || '').trim();
    state.sound = safeGet(LS.sound) !== '0';
    state.room = DEFAULT_ROOM;

    syncRoomUI();
    soundToggle.checked = state.sound;

    renderCached();
    updateSendState();
    startAccess();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
