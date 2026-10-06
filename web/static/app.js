// Search, filters and order on the knowledgebase page; search and filters on
// the Summary Report page; copy buttons on Lean blocks; math on the problem pages.

(function knowledgebase() {
  const root = document.getElementById('kb');
  if (!root) return;
  const grouped = document.getElementById('grouped');
  const flat = document.getElementById('flat');
  const empty = document.getElementById('empty');
  const entries = [...grouped.querySelectorAll('.entry')];
  const home = new Map(entries.map(el => [el, el.parentNode]));
  // The topic and domain each entry is counted under in the sidebar.
  const under = new Map(entries.map(el => [el, [el.parentNode.id, el.parentNode.closest('.domain').id]]));
  const sections = [...grouped.querySelectorAll('.topic, .domain')];
  const tocLinks = [...document.querySelectorAll('.toc a[data-sec]')];
  const count = document.getElementById('count');
  const clear = document.getElementById('clear');
  const q = document.getElementById('q');
  const domain = document.getElementById('f-domain');
  const sort = document.getElementById('f-sort');
  const lean = document.getElementById('f-lean');
  const community = document.getElementById('f-community');
  const kinds = [...document.querySelectorAll('.seg [data-kind]')];
  const total = entries.length;
  const DEFAULTS = {q: '', kind: 'all', domain: 'all', sort: 'topic', lean: '', community: ''};
  const state = {...DEFAULTS};

  // The search text is normalised the way build.py normalises each entry.
  const norm = s => s.toLowerCase().replace(/[_.\s]+/g, ' ').trim();

  // Filters live in the query string, so a filtered view can be shared and
  // survives a reload; the hash is left alone for the topic anchors, and the
  // graph's own keys in the query string are left alone too.
  function readUrl() {
    const p = new URLSearchParams(location.search);
    for (const k of Object.keys(DEFAULTS)) if (p.has(k)) state[k] = p.get(k);
  }
  function writeUrl() {
    const p = new URLSearchParams(location.search);
    for (const [k, v] of Object.entries(state)) if (v !== DEFAULTS[k]) p.set(k, v); else p.delete(k);
    const s = p.toString();
    try { history.replaceState(null, '', (s ? '?' + s : location.pathname) + location.hash); } catch (_) {}
  }
  function syncControls() {
    q.value = state.q;
    domain.value = [...domain.options].some(o => o.value === state.domain) ? state.domain : 'all';
    state.domain = domain.value;
    sort.value = state.sort === 'new' ? 'new' : 'topic';
    lean.checked = state.lean === '1';
    if (community) community.checked = state.community === '1';
    for (const b of kinds) b.setAttribute('aria-pressed', String(b.dataset.kind === state.kind));
  }

  let arranged = 'topic';
  function arrange() {
    const mode = state.sort === 'new' ? 'new' : 'topic';
    if (mode === arranged) return;
    arranged = mode;
    if (mode === 'new') {
      const order = [...entries].sort((a, b) => b.dataset.t - a.dataset.t || b.dataset.seq - a.dataset.seq);
      flat.append(...order);
    } else {
      for (const el of entries) home.get(el).appendChild(el);
    }
    grouped.hidden = mode === 'new';
    flat.hidden = mode !== 'new';
    root.classList.toggle('grouped', mode !== 'new');
  }

  function apply() {
    arrange();
    const words = norm(state.q).split(' ').filter(Boolean);
    let shown = 0;
    for (const el of entries) {
      const ok = words.every(w => el.dataset.q.includes(w))
        && (state.kind === 'all' || el.dataset.kind === state.kind)
        && (state.domain === 'all' || el.dataset.domain === state.domain)
        && (state.community !== '1' || el.dataset.community === '1');
      el.classList.toggle('hidden', !ok);
      if (ok) shown++;
    }
    const counts = {};
    for (const el of entries) {
      if (el.classList.contains('hidden')) continue;
      for (const id of under.get(el)) counts[id] = (counts[id] || 0) + 1;
    }
    for (const sec of sections) {
      sec.classList.toggle('hidden', !counts[sec.id]);
      const n = sec.querySelector(':scope > .dhead .n');
      if (n) n.textContent = counts[sec.id] || 0;
    }
    for (const a of tocLinks) {
      const n = counts[a.dataset.sec] || 0;
      a.querySelector('.c').textContent = n;
      a.classList.toggle('none', n === 0);
    }
    root.classList.toggle('show-lean', state.lean === '1');
    const filtered = Object.keys(DEFAULTS).some(k => k !== 'sort' && k !== 'lean' && state[k] !== DEFAULTS[k]);
    count.textContent = filtered ? `${shown} of ${total} declarations` : `${total} declarations`;
    clear.hidden = !filtered;
    empty.hidden = shown !== 0;
    writeUrl();
  }

  function reset() {
    Object.assign(state, {q: '', kind: 'all', domain: 'all', community: ''});
    syncControls();
    apply();
  }

  q.addEventListener('input', () => { state.q = q.value; apply(); });
  q.addEventListener('keydown', ev => { if (ev.key === 'Escape' && q.value) { ev.preventDefault(); state.q = ''; q.value = ''; apply(); } });
  domain.addEventListener('change', () => { state.domain = domain.value; apply(); });
  sort.addEventListener('change', () => { state.sort = sort.value; apply(); });
  lean.addEventListener('change', () => { state.lean = lean.checked ? '1' : ''; apply(); });
  if (community) community.addEventListener('change', () => { state.community = community.checked ? '1' : ''; apply(); });
  for (const b of kinds) b.addEventListener('click', () => { state.kind = b.dataset.kind; syncControls(); apply(); });
  clear.addEventListener('click', reset);
  empty.querySelector('[data-clear]').addEventListener('click', reset);

  // "/" jumps to the search box from anywhere on the page.
  document.addEventListener('keydown', ev => {
    if (ev.key !== '/' || ev.metaKey || ev.ctrlKey || ev.altKey) return;
    const t = ev.target;
    if (t.closest && t.closest('input, textarea, select, [contenteditable]')) return;
    ev.preventDefault();
    q.focus();
    q.select();
  });

  // A topic link in the list ordered by date goes back to the grouped list
  // first, or there would be nothing to scroll to.
  for (const a of tocLinks) {
    a.addEventListener('click', () => {
      if (state.sort === 'new') { state.sort = 'topic'; syncControls(); apply(); }
      const toc = document.getElementById('toc');
      if (toc && matchMedia('(max-width: 900px)').matches) toc.open = false;
    });
  }

  // The topic list is open beside the list on a wide screen and folded
  // above them on a narrow one.
  const toc = document.getElementById('toc');
  const wide = matchMedia('(min-width: 901px)');
  const fold = () => { if (toc) toc.open = wide.matches; };
  fold();
  if (wide.addEventListener) wide.addEventListener('change', fold);

  // Mark the topic being read in the sidebar.
  if ('IntersectionObserver' in window) {
    const byId = new Map(tocLinks.map(a => [a.dataset.sec, a]));
    const visible = new Set();
    const io = new IntersectionObserver(items => {
      for (const it of items) {
        if (it.isIntersecting) visible.add(it.target.id); else visible.delete(it.target.id);
      }
      const first = sections.find(s => s.classList.contains('topic') && visible.has(s.id));
      for (const a of tocLinks) a.classList.toggle('here', !!first && a.dataset.sec === first.id);
    }, {rootMargin: '-140px 0px -55% 0px'});
    for (const s of sections) if (s.classList.contains('topic') && byId.has(s.id)) io.observe(s);
  }

  readUrl();
  syncControls();
  apply();
})();

(function reports() {
  // The Summary Report page: search, the period tag and the month.
  const list = document.getElementById('r-list');
  if (!list) return;
  const items = [...list.querySelectorAll('.rp')];
  const q = document.getElementById('rq');
  const month = document.getElementById('r-month');
  const periods = [...document.querySelectorAll('.seg [data-period]')];
  const count = document.getElementById('r-count');
  const clear = document.getElementById('r-clear');
  const empty = document.getElementById('r-empty');
  const DEFAULTS = {q: '', period: 'all', month: 'all'};
  const state = {...DEFAULTS};
  const norm = t => t.toLowerCase().replace(/[_.\s]+/g, ' ').trim();

  function apply() {
    const words = norm(state.q).split(' ').filter(Boolean);
    let shown = 0;
    for (const el of items) {
      const ok = (state.period === 'all' || el.dataset.period === state.period)
        && (state.month === 'all' || el.dataset.months.split(' ').includes(state.month))
        && words.every(w => el.dataset.q.includes(w));
      el.hidden = !ok;
      if (ok) shown++;
    }
    const filtered = Object.keys(DEFAULTS).some(k => state[k] !== DEFAULTS[k]);
    const noun = n => `${n} report${n === 1 ? '' : 's'}`;
    count.textContent = filtered ? `${shown} of ${noun(items.length)}` : noun(items.length);
    clear.hidden = !filtered;
    empty.hidden = shown !== 0;
    const p = new URLSearchParams(location.search);
    for (const [k, v] of Object.entries(state)) if (v !== DEFAULTS[k]) p.set(k, v); else p.delete(k);
    const s = p.toString();
    try { history.replaceState(null, '', (s ? '?' + s : location.pathname) + location.hash); } catch (_) {}
  }
  function sync() {
    q.value = state.q;
    month.value = [...month.options].some(o => o.value === state.month) ? state.month : 'all';
    state.month = month.value;
    for (const b of periods) b.setAttribute('aria-pressed', String(b.dataset.period === state.period));
  }
  function reset() { Object.assign(state, DEFAULTS); sync(); apply(); }

  const p = new URLSearchParams(location.search);
  for (const k of Object.keys(DEFAULTS)) if (p.has(k)) state[k] = p.get(k);
  q.addEventListener('input', () => { state.q = q.value; apply(); });
  q.addEventListener('keydown', ev => { if (ev.key === 'Escape' && q.value) { ev.preventDefault(); state.q = ''; q.value = ''; apply(); } });
  month.addEventListener('change', () => { state.month = month.value; apply(); });
  for (const b of periods) b.addEventListener('click', () => { state.period = b.dataset.period; sync(); apply(); });
  clear.addEventListener('click', reset);
  empty.querySelector('[data-clear]').addEventListener('click', reset);
  document.addEventListener('keydown', ev => {
    if (ev.key !== '/' || ev.metaKey || ev.ctrlKey || ev.altKey) return;
    if (ev.target.closest && ev.target.closest('input, textarea, select, [contenteditable]')) return;
    ev.preventDefault();
    q.focus();
  });
  sync();
  apply();
})();

(function copyButtons() {
  if (!navigator.clipboard) return;
  for (const btn of document.querySelectorAll('.codebox .copy')) {
    const pre = btn.parentNode.querySelector('pre');
    btn.hidden = false;
    btn.addEventListener('click', async () => {
      try {
        await navigator.clipboard.writeText(pre.innerText);
        btn.textContent = 'Copied';
      } catch (_) {
        btn.textContent = 'Copy failed';
      }
      setTimeout(() => { btn.textContent = 'Copy'; }, 1600);
    });
  }
})();

(function proofWindow() {
  // The home page's featured results: one tab per theorem.
  const tabs = [...document.querySelectorAll('.pw-tab')];
  const panels = [...document.querySelectorAll('.pw-panel')];
  for (const tab of tabs) {
    tab.addEventListener('click', () => {
      for (const t of tabs) {
        const on = t === tab;
        t.classList.toggle('on', on);
        t.setAttribute('aria-selected', on ? 'true' : 'false');
      }
      for (const p of panels) p.classList.toggle('hidden', p.dataset.pw !== tab.dataset.pw);
    });
  }
})();

window.addEventListener('DOMContentLoaded', () => {
  // KaTeX is loaded only on pages that show submitted statements, and only
  // elements marked .math are rendered, so a "$21" elsewhere stays a price.
  if (typeof renderMathInElement !== 'function') return;
  for (const el of document.querySelectorAll('.math')) {
    renderMathInElement(el, {
      delimiters: [
        {left: '$$', right: '$$', display: true},
        {left: '\\[', right: '\\]', display: true},
        {left: '$', right: '$', display: false},
        {left: '\\(', right: '\\)', display: false},
      ],
      throwOnError: false,
    });
  }
});
