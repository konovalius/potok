/*
  «Поток» — общий чат. Логика клиента.
  Транспорт: публичный релей ntfy.sh (JSON POST на отправку + SSE на приём).
  Без серверного кода: сайт статический, вся синхронизация — через релей.
*/
(() => {
  'use strict';

  // ── Константы ───────────────────────────────────────────────
  const RELAY = 'https://ntfy.sh';
  const TOPIC_PREFIX = 'autoclaw-chat-ru-';
  const DEFAULT_ROOM = 'общий';
  const DEFAULT_TOPIC = 'general';
  const MAX_TEXT = 1200;
  const CACHE_LIMIT = 80;
  const DOM_LIMIT = 300;
  const GROUP_WINDOW = 5 * 60 * 1000; // 5 минут — окно склейки сообщений одного автора
  const LIVE_WINDOW = 60 * 1000;      // старше минуты — считаем историей (без звука и счётчика)
  const LS = { name: 'potok.v1.name', sound: 'potok.v1.sound', room: 'potok.v1.room' };

  // ── Состояние ───────────────────────────────────────────────
  const state = {
    name: '',
    sound: true,
    room: DEFAULT_ROOM,
    seen: new Set(),        // id сообщений, уже отрисованных (дедупликация SSE-реплеев)
    pending: new Map(),     // tmpId -> { el, st, text, tries, failed }
    unread: 0,
    msgCount: 0,
    lastDay: '',
    lastAuthor: '',
    lastTime: 0,
    connectedOnce: false,
    gotData: false,
    baseTitle: 'Поток — общий чат'
  };

  let es = null;
  let slowTimer = null;
  let failTimer = null;
  let audioCtx = null;
  let localCh = null;

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

  // Транслитерация для темы комнаты (в темах ntfy допустимы только [a-zA-Z0-9_-])
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
  function topicFor(room) {
    return TOPIC_PREFIX + (room === DEFAULT_ROOM ? DEFAULT_TOPIC : slugifyRoom(room));
  }
  function normalizeRoom(raw) {
    let label = String(raw || '').trim().replace(/\s+/g, ' ');
    if (label.length > 32) label = label.slice(0, 32);
    if (!label || label.toLowerCase() === DEFAULT_ROOM) label = DEFAULT_ROOM;
    return label;
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
  const nameGate = $('nameGate');
  const gateForm = $('gateForm');
  const nameInput = $('nameInput');
  const nameError = $('nameError');
  const settings = $('settings');
  const settingsForm = $('settingsForm');
  const settingsName = $('settingsName');
  const settingsNameError = $('settingsNameError');
  const settingsRoom = $('settingsRoom');
  const soundToggle = $('soundToggle');
  const settingsClose = $('settingsClose');
  const copyLinkBtn = $('copyLinkBtn');
  const toasts = $('toasts');
  const modeNotice = $('modeNotice');
  const modeNoticeClose = $('modeNoticeClose');
  const legalLine = $('legalLine');
  const aboutHow = $('aboutHow');

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
  const CONN_TEXT = { connecting: 'подключение…', online: 'в сети', reconnecting: 'переподключение…', error: 'нет связи', local: 'локально' };
  function setConn(mode) {
    connBox.dataset.state = mode;
    connText.textContent = CONN_TEXT[mode] || mode;
  }
  function showBanner(text) { offlineText.textContent = text; offlineBanner.hidden = false; }
  function hideBanner() { offlineBanner.hidden = true; }

  function clearTimers() { clearTimeout(slowTimer); clearTimeout(failTimer); }

  retryBtn.addEventListener('click', () => { hideBanner(); connect(); });
  modeNoticeClose.addEventListener('click', () => { modeNotice.hidden = true; safeSet('potok.v1.notice_off', '1'); });
  emptyCta.addEventListener('click', () => composerInput.focus());

  // ── Пустая комната / скелетон ───────────────────────────────
  function removeSkeleton() {
    if (!skeleton.hidden) skeleton.hidden = true;
    if (!slowNote.hidden) slowNote.hidden = true;
  }
  function maybeShowEmpty() {
    if (state.msgCount === 0 && skeleton.hidden) emptyState.hidden = false;
  }
  function hideEmpty() { if (!emptyState.hidden) emptyState.hidden = true; }

  // ── Кэш сообщений (мгновенная отрисовка и офлайн-чтение) ────
  const cacheKey = () => 'potok.v1.cache.' + topicFor(state.room);
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
        first.remove(); state.msgCount--;
      } else if (first.classList.contains('day') || first.classList.contains('note')) {
        first.remove();
      } else {
        return;
      }
    }
  }

  function renderMessage(msg) {
    const { name, text, time, mine } = msg;
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

    if (msg.pending || isNearBottom()) {
      requestAnimationFrame(() => scrollToBottom(msg.pending ? 'smooth' : 'auto'));
    }
    return { row, st };
  }

  // ── Сеть: подписка (SSE) ────────────────────────────────────
  function connect() {
    if (state.mode === 'local') return;
    if (es) { es.close(); es = null; }
    setConn('connecting');
    clearTimers();
    slowTimer = setTimeout(() => { if (!state.gotData) slowNote.hidden = false; }, 12000);
    failTimer = setTimeout(() => {
      if (!state.connectedOnce) {
        setConn('error');
        showBanner('Нет ответа от релея. Проверьте интернет — мы продолжаем попытки.');
        maybeShowEmpty();
      }
    }, 25000);

    try {
      es = new EventSource(RELAY + '/' + topicFor(state.room) + '/sse?since=12h');
    } catch (e) {
      setConn('error');
      showBanner('Не удалось подключиться к релею.');
      return;
    }

    es.addEventListener('open', () => {
      state.connectedOnce = true;
      state.gotData = true;
      clearTimers();
      slowNote.hidden = true;
      setConn('online');
      hideBanner();
      removeSkeleton();
      maybeShowEmpty();
      flushFailed();
    });

    es.addEventListener('message', onRelayMessage);

    es.addEventListener('error', () => {
      if (state.connectedOnce) {
        setConn('reconnecting');
        showBanner('Связь с релеем пропала — сообщения могут не доходить. Переподключаемся…');
      } else {
        setConn('connecting');
      }
      // EventSource переподключается сам; кнопка «Переподключиться» ускоряет процесс
    });
  }

  function onRelayMessage(ev) {
    let d = null;
    try { d = JSON.parse(ev.data); } catch (e) { return; }
    if (!d || d.event !== 'message' || !d.id) return;

    state.gotData = true;
    slowNote.hidden = true;

    if (state.seen.has(d.id)) return; // реплей истории — уже видели

    const name = (typeof d.title === 'string' && d.title.trim()) || 'Гость';
    const text = typeof d.message === 'string' ? d.message : '';
    const time = typeof d.time === 'number' ? d.time * 1000 : Date.now();

    // Эхо собственного сообщения: переиспользуем оптимистичный пузырь,
    // чтобы не задвоить сообщение и не сломать группировку с соседями.
    if (name === state.name) {
      for (const [tmpId, p] of state.pending) {
        if (!p.delivered && p.text === text && Math.abs(time - p.time) < 120000) {
          p.delivered = true;
          state.seen.add(d.id);
          state.pending.delete(tmpId);
          if (p.el.isConnected) {
            p.el.classList.remove('msg-pending', 'msg-error');
            if (p.st && p.st.isConnected) p.st.remove();
          }
          removeSkeleton();
          addToCache({ id: d.id, n: name, t: time, x: text });
          return;
        }
      }
    }

    state.seen.add(d.id);
    const mine = name === state.name;

    renderMessage({ name, text, time, mine });
    removeSkeleton();
    addToCache({ id: d.id, n: name, t: time, x: text });

    const age = Date.now() - time;
    if (!mine && age < LIVE_WINDOW) {
      blip();
      if (document.hidden || !isNearBottom()) {
        state.unread++;
      }
      updateUnreadUI();
    }
  }

  // ── Сеть: отправка ──────────────────────────────────────────
  async function fetchTimeout(url, opts, ms) {
    const ctl = new AbortController();
    const t = setTimeout(() => ctl.abort(), ms);
    try { return await fetch(url, Object.assign({}, opts, { signal: ctl.signal })); }
    finally { clearTimeout(t); }
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

  async function attemptPublish(tmpId) {
    const p = state.pending.get(tmpId);
    if (!p) return;
    if (state.mode === 'local') { localPublish(tmpId); return; }
    p.tries++;
    try {
      const res = await fetchTimeout(RELAY + '/', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ topic: topicFor(state.room), title: state.name, message: p.text })
      }, 12000);
      if (!res.ok) { const err = new Error('HTTP ' + res.status); err.status = res.status; throw err; }
      const info = await res.json().catch(() => null);
      state.pending.delete(tmpId);
      if (p.delivered) return; // эхо уже финализировало пузырь (гонка POST/SSE)
      if (info && info.id && state.seen.has(info.id)) {
        if (p.el.isConnected) { p.el.remove(); state.msgCount--; } // эхо уже пришло раньше — временный пузырь не нужен
      } else {
        if (info && info.id) state.seen.add(info.id); // чтобы эхо не задвоило
        if (p.el.isConnected) {
          p.el.classList.remove('msg-pending');
          if (p.st && p.st.isConnected) p.st.remove();
        }
        addToCache({ id: (info && info.id) || tmpId, n: state.name, t: Date.now(), x: p.text });
      }
    } catch (err) {
      if (p.delivered) return; // сообщение уже доставлено, несмотря на сбой чтения ответа
      const retryable = !err.status || err.status >= 500 || err.status === 429 || err.name === 'AbortError';
      if (p.tries < 3 && retryable) {
        setTimeout(() => attemptPublish(tmpId), 900 * p.tries);
      } else {
        p.failed = true;
        if (p.el.isConnected) {
          p.el.classList.add('msg-error');
          p.el.classList.remove('msg-pending');
        }
        setStatusNode(p, 'failed');
        toast(err.status === 429
          ? 'Слишком часто — подождите пару секунд и нажмите «повторить»'
          : 'Сообщение не отправилось. Нажмите «повторить» под ним.');
      }
    }
  }

  function retryMessage(tmpId) {
    const p = state.pending.get(tmpId);
    if (!p) return;
    p.failed = false;
    p.tries = 0;
    if (p.el.isConnected) {
      p.el.classList.remove('msg-error');
      p.el.classList.add('msg-pending');
    }
    setStatusNode(p, 'pending');
    attemptPublish(tmpId);
  }

  function flushFailed() {
    state.pending.forEach((p, id) => {
      if (p.failed) retryMessage(id);
    });
  }

  // ── Транспорт: релей или локальный режим ────────────────
  async function probeRelay() {
    try {
      const ctl = new AbortController();
      const t = setTimeout(() => ctl.abort(), 4000);
      try {
        // режим no-cors: достаточно проверить достижимость, тело не нужно
        await fetch(RELAY + '/v1/health', { mode: 'no-cors', cache: 'no-store', signal: ctl.signal });
        return true;
      } finally {
        clearTimeout(t);
      }
    } catch (e) {
      return false;
    }
  }

  async function initTransport() {
    setConn('connecting');
    const reachable = await probeRelay();
    if (reachable) {
      state.mode = 'relay';
      updateModeTexts();
      connect();
    } else {
      startLocalMode();
    }
  }

  function startLocalMode() {
    state.mode = 'local';
    clearTimers();
    hideBanner();
    removeSkeleton();
    maybeShowEmpty();
    setConn('local');
    updateModeTexts();
    openLocalChannel();
    if (!safeGet('potok.v1.notice_off')) modeNotice.hidden = false;
  }

  function openLocalChannel() {
    closeLocalChannel();
    try {
      localCh = new BroadcastChannel('potok.v1.' + topicFor(state.room));
      localCh.addEventListener('message', onLocalMessage);
    } catch (e) {
      localCh = null; // экзотический браузер без BroadcastChannel
    }
  }

  function closeLocalChannel() {
    if (localCh) { try { localCh.close(); } catch (e) {} localCh = null; }
  }

  function onLocalMessage(ev) {
    const d = ev && ev.data;
    if (!d || d.type !== 'msg' || !d.body || !d.body.id) return;
    const m = d.body;
    if (state.seen.has(m.id)) return;
    state.seen.add(m.id);
    const name = (typeof m.title === 'string' && m.title.trim()) || 'Гость';
    const text = typeof m.message === 'string' ? m.message : '';
    const time = typeof m.time === 'number' ? m.time * 1000 : Date.now();
    const mine = name === state.name;
    renderMessage({ name, text, time, mine });
    removeSkeleton();
    addToCache({ id: m.id, n: name, t: time, x: text });
    if (!mine) {
      blip();
      if (document.hidden || !isNearBottom()) state.unread++;
      updateUnreadUI();
    }
  }

  function updateModeTexts() {
    const local = state.mode === 'local';
    legalLine.textContent = local
      ? 'Локальный режим: сообщения живут в этом браузере и синхронизируются между его окнами.'
      : 'Демо-сайт без сервера: сообщения передаются через публичный релей ntfy.sh, история хранится ≈12 часов. Не отправляйте личные данные.';
    aboutHow.textContent = local
      ? 'Как это работает: сейчас включён локальный режим — превью блокирует внешние соединения, поэтому сообщения синхронизируются между окнами этого браузера. При размещении сайта на обычном хостинге включится сетевой режим с общей комнатой.'
      : 'Как это работает: сайт статический, без бэкенда. Сообщения уходят в публичную комнату релея ntfy.sh и мгновенно раздаются всем, кто её открыл; история хранится около 12 часов. Не пишите сюда личные данные.';
  }

  function localPublish(tmpId) {
    const p = state.pending.get(tmpId);
    if (!p) return;
    const d = { id: 'loc-' + tmpId, title: state.name, message: p.text, time: Math.round(p.time / 1000) };
    try {
      if (localCh) localCh.postMessage({ type: 'msg', body: d });
      state.pending.delete(tmpId);
      state.seen.add(d.id);
      if (p.el.isConnected) {
        p.el.classList.remove('msg-pending');
        if (p.st && p.st.isConnected) p.st.remove();
      }
      addToCache({ id: d.id, n: state.name, t: p.time, x: p.text });
    } catch (e) {
      p.failed = true;
      if (p.el.isConnected) { p.el.classList.add('msg-error'); p.el.classList.remove('msg-pending'); }
      setStatusNode(p, 'failed');
    }
  }

  function sendText(text) {
    if (!state.name) { openGate(); return; }
    const t0 = Date.now();
    const tmpId = 't' + (window.crypto && crypto.randomUUID ? crypto.randomUUID() : t0 + '-' + Math.random().toString(16).slice(2));
    const built = renderMessage({ name: state.name, text, time: t0, mine: true, pending: true });
    const p = { id: tmpId, el: built.row, st: built.st, text, time: t0, tries: 0, failed: false, delivered: false };
    state.pending.set(tmpId, p);
    attemptPublish(tmpId);
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
  function openGate() {
    nameGate.hidden = false;
    nameInput.value = state.name || nameInput.value;
    setTimeout(() => nameInput.focus(), 80);
  }
  function hideGate() {
    nameGate.hidden = true;
    try { document.documentElement.classList.add('has-name'); } catch (e) {}
  }

  gateForm.addEventListener('submit', (e) => {
    e.preventDefault();
    const v = nameInput.value.trim();
    const err = validateName(v);
    if (err) { showFieldError(nameInput, nameError, err); nameInput.focus(); return; }
    clearFieldError(nameInput, nameError);
    applyName(v);
    hideGate();
    ensureAudio();
    addNote('Вы вошли в комнату «' + state.room + '»');
    composerInput.focus();
  });
  nameInput.addEventListener('input', () => {
    if (!nameError.hidden) {
      const err = validateName(nameInput.value.trim());
      if (!err) clearFieldError(nameInput, nameError);
    }
  });

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
    state.connectedOnce = false;
    state.gotData = false;
    state.unread = 0;
    skeleton.hidden = false;
    slowNote.hidden = true;
    emptyState.hidden = true;
    syncRoomUI();
    renderCached();
    addNote('Комната: «' + label + '»');
    closeLocalChannel();
    if (state.mode === 'relay') {
      connect();
    } else {
      hideBanner();
      setConn('local');
      openLocalChannel();
      removeSkeleton();
      maybeShowEmpty();
    }
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

  // ── Кэш на старте ───────────────────────────────────────────
  function renderCached() {
    const items = loadCache();
    if (!items.length) return;
    let count = 0;
    for (const it of items) {
      if (!it || !it.id || state.seen.has(it.id)) continue;
      state.seen.add(it.id);
      renderMessage({ name: it.n || 'Гость', text: it.x || '', time: it.t || Date.now(), mine: (it.n || '') === state.name, noAnim: true });
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

    if (state.name) {
      applyName(state.name);
      nameGate.hidden = true;
    } else {
      setTimeout(() => nameInput.focus(), 120);
    }

    renderCached();
    updateSendState();
    initTransport();

    if (state.name) setTimeout(() => composerInput.focus(), 160);
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
