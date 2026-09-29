// Search and filters on the results page; math on the problem pages.

(function results() {
  const root = document.getElementById('results');
  if (!root) return;
  const entries = [...root.querySelectorAll('.entry')];
  const topics = [...root.querySelectorAll('.topic')];
  const domains = [...root.querySelectorAll('.domain')];
  const count = document.getElementById('count');
  const total = entries.length;
  const state = {q: '', kind: 'all', domain: 'all', community: 'all'};

  function apply() {
    const q = state.q.trim().toLowerCase();
    let shown = 0;
    for (const el of entries) {
      const ok = (!q || el.dataset.q.includes(q))
        && (state.kind === 'all' || el.dataset.kind === state.kind)
        && (state.domain === 'all' || el.dataset.domain === state.domain)
        && (state.community === 'all' || el.dataset.community === state.community);
      el.classList.toggle('hidden', !ok);
      if (ok) shown++;
    }
    for (const t of topics) t.classList.toggle('hidden', !t.querySelector('.entry:not(.hidden)'));
    for (const d of domains) d.classList.toggle('hidden', !d.querySelector('.entry:not(.hidden)'));
    count.textContent = shown === total ? `${total} declarations` : `${shown} of ${total} declarations`;
  }

  document.getElementById('q').addEventListener('input', ev => { state.q = ev.target.value; apply(); });
  for (const chip of document.querySelectorAll('.chip[data-filter]')) {
    chip.addEventListener('click', () => {
      const group = chip.dataset.filter;
      if (chip.hasAttribute('data-toggle')) {
        // An on/off filter that sits beside a group without being part of it.
        const on = !chip.classList.contains('on');
        chip.classList.toggle('on', on);
        state[group] = on ? chip.dataset.value : 'all';
      } else {
        state[group] = chip.dataset.value;
        document.querySelectorAll(`.chip[data-filter="${group}"]:not([data-toggle])`)
          .forEach(c => c.classList.toggle('on', c === chip));
      }
      apply();
    });
  }
  apply();
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
