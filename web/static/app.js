// Search, filters and order on the knowledgebase page; search and filters on
// the Summary Reports page; copy buttons on Lean blocks; share buttons on the
// reports; math on the problem pages.

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
  // The Summary Reports page: search, the period tag and the month.
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

(function shareButtons() {
  // A report, its story or one result: on a phone, the share sheet; elsewhere
  // the text and the link to it, copied, ready to paste into a post.
  const coarse = window.matchMedia && matchMedia('(pointer: coarse)').matches;
  for (const btn of document.querySelectorAll('button.share')) {
    if (!navigator.clipboard && !(coarse && navigator.share)) continue;
    btn.hidden = false;
    const label = btn.textContent;
    btn.addEventListener('click', async () => {
      const url = location.origin + location.pathname + (btn.dataset.anchor ? '#' + btn.dataset.anchor : '');
      const text = btn.dataset.text;
      if (coarse && navigator.share) {
        try { await navigator.share({title: document.title, text, url}); } catch (_) { /* dismissed */ }
        return;
      }
      try {
        await navigator.clipboard.writeText(text + '\n' + url);
        btn.textContent = btn.dataset.done || 'Copied';
      } catch (_) {
        btn.textContent = 'Copy failed';
      }
      setTimeout(() => { btn.textContent = label; }, 1600);
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

(function sourceLines() {
  // A declaration page whose explanation names lines of the source: "lines
  // 3–5" highlights them there. (The link alone already jumps to #L3.)
  const pre = document.querySelector('pre.lines');
  if (!pre) return;
  const lineEls = [...pre.querySelectorAll('.ln')];
  let lit = [];
  function show(a, b) {
    for (const el of lit) el.classList.remove('ex');
    lit = lineEls.slice(a - 1, b);
    for (const el of lit) el.classList.add('ex');
    if (lit[0]) lit[0].scrollIntoView({block: 'center', behavior: 'smooth'});
  }
  for (const a of document.querySelectorAll('a.lines')) {
    a.addEventListener('click', ev => {
      ev.preventDefault();
      const l1 = +a.dataset.l1, l2 = +a.dataset.l2;
      try { history.replaceState(null, '', '#L' + l1); } catch (_) {}
      show(l1, l2);
      document.dispatchEvent(new CustomEvent('aftd:lines', {detail: {l1, l2}}));
    });
  }
  const m = /^#L(\d+)$/.exec(location.hash);
  if (m) show(+m[1], +m[1]);
})();

(function stepper() {
  // The proof stepper: Lean's goals before and after each tactic, as an
  // infoview shows them, read from trace.json beside the page -- fetched only
  // when the reader gets near the proof. Every string from the trace goes in
  // as text, never as markup.
  const box = document.querySelector('.stepper[data-trace]');
  if (!box) return;
  const pre = box.querySelector('pre.lines');
  const panel = box.querySelector('.st-panel');
  const lineEls = [...pre.querySelectorAll('.ln')];
  const pos = panel.querySelector('.st-pos');
  const tac = panel.querySelector('.st-tac');
  const beforeEl = panel.querySelector('.st-before');
  const afterEl = panel.querySelector('.st-after');
  const usedEl = panel.querySelector('.st-used');
  const prev = panel.querySelector('.st-prev');
  const next = panel.querySelector('.st-next');
  const hl = (window.CSS && CSS.highlights && window.Highlight) ? CSS.highlights : null;
  let T = null, cur = -1, loading = null, pending = null;
  const byLine = new Map();  // line -> indices of the steps that start there

  const el = (tag, cls, text) => {
    const x = document.createElement(tag);
    if (cls) x.className = cls;
    if (text != null) x.textContent = text;
    return x;
  };
  const goalText = g => T.goals[g].map(i => T.lines[i]).join('\n');

  // One goal, laid out like the infoview: an optional case tag, the
  // hypotheses with their names picked out, then the target after ⊢.
  // `seen` holds the lines of the state before; what is new is marked.
  function goalEl(text, seen) {
    const box = el('div', 'goal');
    let last = null;
    text.split('\n').forEach((line, i) => {
      if (last && /^\s/.test(line) && !line.trimStart().startsWith('⊢')) {
        last.append('\n' + line);  // a long type, wrapped by Lean's printer
        return;
      }
      let row;
      if (i === 0 && /^case /.test(line)) row = el('div', 'g-case', line);
      else if (line.startsWith('⊢')) row = el('div', 'g-tgt', line);
      else {
        row = el('div', 'g-hyp');
        const k = line.indexOf(' : ');
        if (k > 0) { row.append(el('span', 'g-name', line.slice(0, k))); row.append(line.slice(k)); }
        else row.textContent = line;
      }
      if (seen && !seen.has(line)) row.classList.add('new');
      box.append(row);
      last = row;
    });
    return box;
  }

  function stateEl(target, ids, more, seen, emptyText) {
    target.replaceChildren();
    if (ids == null) { target.append(el('p', 'g-none', 'Lean did not record this state.')); return; }
    if (!ids.length) { target.append(el('p', 'g-none g-done', emptyText)); return; }
    ids.forEach(g => target.append(goalEl(goalText(g), seen)));
    if (more) target.append(el('p', 'g-none', `… and ${more} more goal${more === 1 ? '' : 's'}`));
  }

  // Columns are Lean's: code points into the line, not UTF-16 units.
  function point(lineEl, col) {
    const w = document.createTreeWalker(lineEl, NodeFilter.SHOW_TEXT);
    let n, left = col, lastNode = null;
    while ((n = w.nextNode())) {
      lastNode = n;
      const s = n.data;
      let i = 0;
      while (i < s.length && left > 0) { i += s.codePointAt(i) > 0xffff ? 2 : 1; left--; }
      if (left === 0 && i < s.length) return [n, i];
      if (left === 0) return [n, s.length];
    }
    return lastNode ? [lastNode, lastNode.data.length] : null;
  }

  function mark(st) {
    for (const x of pre.querySelectorAll('.ln.sel, .ln.span')) x.classList.remove('sel', 'span');
    for (let l = st.line; l <= st.end_line; l++) {
      const x = lineEls[l - 1];
      if (x) x.classList.add(l === st.line ? 'sel' : 'span');
    }
    if (!hl) return;
    try {
      const a = point(lineEls[st.line - 1], st.col), b = point(lineEls[st.end_line - 1], st.end_col);
      if (!a || !b) return;
      const r = new Range();
      r.setStart(a[0], a[1]);
      r.setEnd(b[0], b[1]);
      hl.set('aftd-tactic', new Highlight(r));
    } catch (_) { /* the line highlight is enough */ }
  }

  function select(i, scroll) {
    if (!T || i < 0 || i >= T.steps.length) return;
    cur = i;
    const st = T.steps[i];
    mark(st);
    pos.textContent = `Tactic ${i + 1} of ${T.steps.length} · line ${st.line}`;
    tac.textContent = st.tactic;
    const seen = new Set();
    for (const g of st.before || []) for (const k of T.goals[g]) seen.add(T.lines[k]);
    stateEl(beforeEl, st.before, st.more_before, null, 'No goals.');
    stateEl(afterEl, st.after, st.more_after, st.before ? seen : null,
            'No goals left: this tactic closes its goal.');
    usedEl.replaceChildren();
    if (st.used && st.used.length) {
      usedEl.append('Uses ');
      st.used.forEach((u, k) => { if (k) usedEl.append(', '); usedEl.append(el('code', '', u)); });
    }
    prev.disabled = i === 0;
    next.disabled = i === T.steps.length - 1;
    if (scroll) lineEls[st.line - 1].scrollIntoView({block: 'nearest'});
  }

  function onLine(l) {
    const here = byLine.get(l);
    if (!here) return false;
    // Again on the same line: the next tactic on it.
    const k = here.indexOf(cur);
    select(k >= 0 ? here[(k + 1) % here.length] : here[0], false);
    return true;
  }

  function init(data) {
    T = data;
    T.steps.forEach((st, i) => {
      if (!byLine.has(st.line)) byLine.set(st.line, []);
      byLine.get(st.line).push(i);
    });
    for (const [l] of byLine) {
      const x = lineEls[l - 1];
      if (x) { x.classList.add('t'); x.title = 'Show the goals at this tactic'; }
    }
    pre.classList.add('stepping');
    panel.hidden = false;
    const hint = box.querySelector('.st-hint');
    if (hint) hint.hidden = false;
    select(0, false);
    if (pending) { const p = pending; pending = null; p(); }
  }

  function load() {
    if (!loading) {
      loading = fetch(box.dataset.trace)
        .then(r => { if (!r.ok) throw new Error(r.status); return r.json(); })
        .then(init)
        .catch(() => { /* the source is still there to read */ });
    }
    return loading;
  }

  pre.addEventListener('click', ev => {
    const x = ev.target.closest('.ln');
    if (!x || !T) return;
    if (window.getSelection && String(getSelection()).length) return;  // copying, not choosing
    onLine(+x.dataset.l);
  });
  prev.addEventListener('click', () => select(cur - 1, true));
  next.addEventListener('click', () => select(cur + 1, true));
  box.addEventListener('keydown', ev => {
    if (!T || ev.metaKey || ev.ctrlKey || ev.altKey) return;
    if (ev.key === 'ArrowLeft' || ev.key === 'k') { ev.preventDefault(); select(cur - 1, true); }
    else if (ev.key === 'ArrowRight' || ev.key === 'j') { ev.preventDefault(); select(cur + 1, true); }
  });
  // Outside any field, the arrows step too, once the stepper is on screen.
  let inView = false;
  document.addEventListener('keydown', ev => {
    if (!T || !inView || ev.metaKey || ev.ctrlKey || ev.altKey || box.contains(ev.target)) return;
    if (ev.target.closest && ev.target.closest('input, textarea, select, [contenteditable]')) return;
    if (ev.key === 'ArrowLeft') { ev.preventDefault(); select(cur - 1, true); }
    else if (ev.key === 'ArrowRight') { ev.preventDefault(); select(cur + 1, true); }
  });
  // An explanation's "lines 3–5": the first tactic there.
  document.addEventListener('aftd:lines', ev => {
    const go = () => {
      for (let l = ev.detail.l1; l <= ev.detail.l2; l++) if (byLine.has(l)) { select(byLine.get(l)[0], false); return; }
    };
    if (T) go(); else { pending = go; load(); }
  });

  if ('IntersectionObserver' in window) {
    const io = new IntersectionObserver(items => {
      for (const it of items) {
        inView = it.isIntersecting;
        if (it.isIntersecting) load();
      }
    }, {rootMargin: '400px 0px'});
    io.observe(box);
  } else {
    load();
  }
})();

window.addEventListener('DOMContentLoaded', () => {
  // KaTeX is loaded only on pages that show submitted statements, and only
  // elements marked .math are rendered, so a "$21" elsewhere stays a price.
  if (typeof renderMathInElement !== 'function') return;
  const render = (el) => renderMathInElement(el, {
    delimiters: [
      {left: '$$', right: '$$', display: true},
      {left: '\\[', right: '\\]', display: true},
      {left: '$', right: '$', display: false},
      {left: '\\(', right: '\\)', display: false},
    ],
    // What imported statements (TCSlib's) write that KaTeX does not know.
    macros: {
      '\\bbr': '\\mathbb{R}', '\\bbn': '\\mathbb{N}', '\\bbz': '\\mathbb{Z}',
      '\\bbf': '\\mathbb{F}', '\\bbP': '\\mathbb{P}', '\\E': '\\mathbb{E}',
      '\\abs': '\\left|#1\\right|', '\\norm': '\\left\\|#1\\right\\|',
      '\\dist': '\\operatorname{dist}',
    },
    throwOnError: false,
  });
  // The knowledgebase lists every declaration: typeset each as it comes into
  // view, not thousands of formulas before the page can scroll.
  const els = document.querySelectorAll('.math');
  if (!('IntersectionObserver' in window)) { els.forEach(render); return; }
  const io = new IntersectionObserver((seen) => {
    for (const x of seen) {
      if (x.isIntersecting) { io.unobserve(x.target); render(x.target); }
    }
  }, {rootMargin: '600px 0px'});
  els.forEach((el) => io.observe(el));
});
