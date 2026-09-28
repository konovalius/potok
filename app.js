/*
  «Поток» — закрытый общий чат. Логика клиента.
  Транспорт: приватная база Supabase (анонимная сессия + код доступа + защита на уровне строк).
  Без серверного кода: сайт статический; доступ и хранение обеспечивает база.
*/
(() => {
  'use strict';

  // ── Конфигурация ────────────────────────────────────────────
  const CONF = window.POTOK_CONFIG || {};
  const sb = (window.supabase && CONF.supabaseUrl && CONF.supabaseAnonKey)
    ? window.supabase.createClient(CONF.supabaseUrl, CONF.supabaseAnonKey)
    : null;

  const DEFAULT_ROOM = 'общий';
  const MAX_TEXT = 2000;
  const CACHE_LIMIT = 80;
  const DOM_LIMIT = 300;
  const HISTORY_LIMIT = 300;
  const GROUP_WINDOW = 5 * 60 * 1000; // 5 минут — окно склейки сообщений одного автора
  const LIVE_WINDOW = 60 * 1000;      // старше минуты — считаем историей (без звука и счётчика)
  const LS = { name: 'potok.v1.name', sound: 'potok.v1.sound', room: 'potok.v1.room' };
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
    baseTitle: 'Поток — общий чат'
  };

  let channel = null;        // realtime-канал текущей комнаты
  let currentUser = null;    // текущий пользователь сессии (для «моё/не моё»)
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
  const settingsRoom = $('settingsRoom');
  const soundToggle = $('soundToggle');
  const settingsClose = $('settingsClose');
  const copyLinkBtn = $('copyLinkBtn');
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
  function toast(text) {
    const t = el('div', 'toast', text);
    let hideTimer = setTimeout(hide, 3400);
    function hide() { t.classList.add('out'); setTimeout(() => t.remove(), 220); }
    t.addEventListener('mouseenter', () => clearTimeout(hideTimer));
    t.addEventListener('focusin', () => clearTimeout(hideTimer));
    t.addEventListener('mouseleave', () => { hideTimer = setTimeout(hide, 1200); });
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
    const { name, text, time, mine, id } = msg;
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
      head.appendChild(el('span', 'msg-name', name));
      head.appendChild(el('span', 'msg-time', timeFmt.format(new Date(time))));
      wrap.appendChild(head);
    }
    const bubble = el('div', 'bubble');
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
      enterChat();
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
  function rowToMessage(row, quiet) {
    const id = String(row.id);
    if (state.seen.has(id)) return;
    const cmid = row.client_msg_id;
    if (cmid && state.pending.has(cmid)) {
      // эхо собственного сообщения — финализируем оптимистичный пузырь
      const p = state.pending.get(cmid);
      p.reconciled = true;
      state.pending.delete(cmid);
      state.seen.add(id);
      if (p.el.isConnected) {
        p.el.classList.remove('msg-pending', 'msg-error');
        if (p.st && p.st.isConnected) p.st.remove();
      }
      attachMessageId(p.el, id);
      addToCache({ id, n: row.author, t: Date.parse(row.created_at), x: row.body, u: row.user_id || null });
      return;
    }
    const name = (typeof row.author === 'string' && row.author.trim()) || 'Гость';
    const time = row.created_at ? Date.parse(row.created_at) : Date.now();
    const mine = isMine(row.user_id, name);
    renderMessage({ name, text: row.body || '', time, mine, noAnim: !!quiet, id });
    state.seen.add(id);
    addToCache({ id, n: name, t: time, x: row.body || '', u: row.user_id || null });
    if (quiet) return;
    const age = Date.now() - time;
    if (!mine && age < LIVE_WINDOW) {
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
      .on('postgres_changes', { event: 'INSERT', schema: 'public', table: 'potok_messages' }, (payload) => {
        const row = payload && payload.new;
        if (!row || row.room !== state.room) return;
        rowToMessage(row, false);
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
        rowToMessage(row, true);
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
    try {
      const { data, error } = await sb
        .from('potok_messages')
        .insert({ room: state.room, author: state.name, body: p.text, client_msg_id: cmid })
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
    if (left <= 220) {
      charCounter.hidden = false;
      charCounter.textContent = 'осталось ' + Math.max(left, 0);
      charCounter.classList.toggle('warn', left <= 80);
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
  function openSettings(focusRoom) {
    settingsName.value = state.name;
    settingsRoom.value = state.room;
    soundToggle.checked = state.sound;
    clearFieldError(settingsName, settingsNameError);
    settings.hidden = false;
    setTimeout(() => (focusRoom ? settingsRoom : settingsName).focus(), 80);
  }
  function closeSettings() {
    settings.hidden = true;
    meBtn.focus();
  }
  meBtn.addEventListener('click', () => openSettings(false));
  roomChip.addEventListener('click', () => openSettings(true));
  settingsClose.addEventListener('click', closeSettings);
  settings.addEventListener('click', (e) => { if (e.target === settings) closeSettings(); });

  settingsForm.addEventListener('submit', (e) => {
    e.preventDefault();
    const v = settingsName.value.trim();
    const err = validateName(v);
    if (err) { showFieldError(settingsName, settingsNameError, err); settingsName.focus(); return; }
    clearFieldError(settingsName, settingsNameError);

    const newRoom = normalizeRoom(settingsRoom.value);
    const nameChanged = v !== state.name;
    const roomChanged = newRoom !== state.room;

    if (nameChanged) {
      applyName(v);
      addNote('Теперь вы пишете как «' + v + '»');
    }
    state.sound = soundToggle.checked;
    safeSet(LS.sound, state.sound ? '1' : '0');
    if (state.sound) ensureAudio();

    closeSettings();
    if (roomChanged) switchRoom(newRoom);
    else toast('Сохранено');
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

  // ── Комнаты ─────────────────────────────────────────────────
  function syncRoomUI() {
    roomLabelEl.textContent = state.room;
    composerInput.placeholder = 'Сообщение в #' + state.room;
    state.baseTitle = state.room === DEFAULT_ROOM ? 'Поток — общий чат' : 'Поток — комната «' + state.room + '»';
    updateUnreadUI();
  }
  function switchRoom(label) {
    state.room = label;
    safeSet(LS.room, label);
    try { history.replaceState(null, '', '#' + encodeURIComponent(label)); } catch (e) {}
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
    addNote('Комната: «' + label + '»');
    unsubscribeChannel();
    if (state.joined) loadRoom();
  }

  function addNote(text) {
    const n = el('div', 'note', text);
    chatList.appendChild(n);
  }

  // ── Приглашение ─────────────────────────────────────────────
  async function copyInvite() {
    const base = location.href.split('#')[0];
    const url = base + '#' + encodeURIComponent(state.room);
    let ok = false;
    try { await navigator.clipboard.writeText(url); ok = true; }
    catch (e) { ok = fallbackCopy(url); }
    toast(ok ? 'Ссылка-приглашение скопирована' : 'Скопируйте адрес из строки браузера');
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

  // ── Кэш на старте ───────────────────────────────────────────
  function renderCached() {
    const items = loadCache();
    if (!items.length) return;
    let count = 0;
    for (const it of items) {
      if (!it || !it.id || state.seen.has(it.id)) continue;
      state.seen.add(it.id);
      const cachedMine = isMine(it.u || null, it.n || '');
      renderMessage({ name: it.n || 'Гость', text: it.x || '', time: it.t || Date.now(), mine: cachedMine, noAnim: true, id: it.id });
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

    let room = '';
    try { room = decodeURIComponent(location.hash.slice(1)).trim(); } catch (e) { room = ''; }
    state.room = normalizeRoom(room || safeGet(LS.room) || DEFAULT_ROOM);
    safeSet(LS.room, state.room);

    syncRoomUI();
    soundToggle.checked = state.sound;

    renderCached();
    updateSendState();
    startAccess();
  }

  window.addEventListener('hashchange', () => {
    let r = '';
    try { r = decodeURIComponent(location.hash.slice(1)).trim(); } catch (e) { r = ''; }
    const nr = normalizeRoom(r || DEFAULT_ROOM);
    if (nr !== state.room) switchRoom(nr);
  });

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
