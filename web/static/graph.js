// The dependency graph page: one node per declaration, one arrow per use.
// No library -- a small force layout on a canvas, fed by the JSON that
// build.py writes into the page.

(function graph() {
  const dataEl = document.getElementById('g-data');
  const canvas = document.getElementById('g-canvas');
  if (!dataEl || !canvas) return;
  const D = JSON.parse(dataEl.textContent);
  const stage = document.getElementById('g-stage');
  const tip = document.getElementById('g-tip');
  const panel = document.getElementById('g-panel');
  const selBox = document.getElementById('g-sel');
  const countEl = document.getElementById('g-count');
  const q = document.getElementById('g-q');
  const hits = document.getElementById('g-hits');
  const ctx = canvas.getContext('2d');
  const reduced = matchMedia('(prefers-reduced-motion: reduce)').matches;
  const root = '../';

  // ------------------------------------------------------------ model
  const norm = s => s.toLowerCase().replace(/[_.\s]+/g, ' ').trim();
  // On the canvas a node is labelled by the end of its name: as many dotted
  // parts as fit in LABEL characters, a longer last part cut short. The full
  // name is in the tooltip and the side panel.
  const LABEL = 24;
  const short = name => {
    const parts = name.split('.');
    let out = parts.pop();
    while (parts.length && out.length + parts[parts.length - 1].length + 1 <= LABEL) out = parts.pop() + '.' + out;
    return out.length > LABEL ? out.slice(0, LABEL - 1) + '…' : out;
  };
  const N = D.nodes.map(([name, def, dom, topic, words, slug], i) => ({
    i, name, label: short(name), def: !!def, dom, topic, words, slug,
    deps: [], users: [], x: 0, y: 0, vx: 0, vy: 0, fx: null, fy: null, placed: false,
    hay: norm(name + ' ' + words + ' ' + topic),
  }));
  for (const [a, b] of D.edges) { N[a].deps.push(b); N[b].users.push(a); }
  for (const n of N) n.r = Math.min(18, 3.6 + 2.3 * Math.sqrt(n.users.length)) * (n.def ? 0.85 : 1);
  // Big nodes are drawn last, so they sit on top and get their labels first.
  const byR = [...N].sort((a, b) => a.r - b.r);

  const state = {defs: false, off: new Set(), sel: -1, chain: false};
  let hover = -1;
  let V = [];          // visible nodes
  let L = [];          // visible edges as [user, used]
  let visible = new Uint8Array(N.length);
  let cone = null;     // with the chain on: the selection, all it uses and all that uses it

  function chainOf(i) {
    const seen = new Set([i]);
    for (const dir of ['deps', 'users']) {
      const stack = [i];
      while (stack.length) {
        for (const j of N[stack.pop()][dir]) if (!seen.has(j)) { seen.add(j); stack.push(j); }
      }
    }
    return seen;
  }

  // The chain is shown whole -- definitions and other domains included --
  // whatever the switches say; they apply to the full picture.
  function shown(n) {
    if (cone) return cone.has(n.i);
    return (state.defs || !n.def) && !state.off.has(n.dom);
  }

  // ------------------------------------------------------------ layout
  // d3-force's model: many-body repulsion, springs along the edges, and a
  // pull towards the domain's own centre so each domain keeps its region.
  let alpha = 1, alphaTarget = 0;
  const ALPHA_MIN = 0.002, DECAY = 1 - Math.pow(ALPHA_MIN, 1 / 300);
  let centres = [];
  let linkCount = new Uint16Array(N.length);

  function hash(s) {
    let h = 2166136261;
    for (let k = 0; k < s.length; k++) { h ^= s.charCodeAt(k); h = Math.imul(h, 16777619); }
    return (h >>> 0) / 4294967296;
  }

  function relayout(heat) {
    cone = state.chain && state.sel >= 0 ? chainOf(state.sel) : null;
    visible = new Uint8Array(N.length);
    V = N.filter(shown);
    for (const n of V) visible[n.i] = 1;
    L = D.edges.filter(([a, b]) => visible[a] && visible[b]);
    linkCount = new Uint16Array(N.length);
    for (const [a, b] of L) { linkCount[a]++; linkCount[b]++; }
    const per = new Map();
    for (const n of V) per.set(n.dom, (per.get(n.dom) || 0) + 1);
    const doms = [...per.keys()].sort((a, b) => a - b);
    const R = doms.length > 1 ? 11 * Math.sqrt(V.length) : 0;
    centres = [];
    doms.forEach((d, k) => {
      const t = -Math.PI / 2 + (2 * Math.PI * k) / doms.length;
      centres[d] = {x: R * Math.cos(t), y: R * Math.sin(t), n: per.get(d)};
    });
    for (const n of V) {
      if (n.placed) continue;
      // A newcomer starts beside a neighbour that is already placed, or
      // somewhere fixed within its domain, so the picture is the same each visit.
      const nb = n.deps.concat(n.users).map(j => N[j]).find(m => visible[m.i] && m.placed);
      const c = centres[n.dom];
      const a = 2 * Math.PI * hash(n.name), rr = (nb ? 12 : 6 * Math.sqrt(c.n)) * (0.3 + hash(n.name + '~'));
      n.x = (nb ? nb.x : c.x) + rr * Math.cos(a);
      n.y = (nb ? nb.y : c.y) + rr * Math.sin(a);
      n.vx = n.vy = 0;
      n.placed = true;
    }
    alpha = Math.max(alpha, heat);
    updateCount();
  }

  function tick() {
    alpha += (alphaTarget - alpha) * DECAY;
    const n = V.length;
    for (let a = 0; a < n; a++) {
      const p = V[a];
      for (let b = a + 1; b < n; b++) {
        const o = V[b];
        let dx = o.x - p.x, dy = o.y - p.y, d2 = dx * dx + dy * dy;
        if (d2 > 360000) continue;
        if (d2 < 1) { dx = (hash(p.name + o.name) - 0.5) || 0.1; dy = 0.5; d2 = dx * dx + dy * dy; }
        const w = (-38 * alpha) / d2;
        p.vx += dx * w; p.vy += dy * w; o.vx -= dx * w; o.vy -= dy * w;
        // Keep discs from overlapping.
        const min = p.r + o.r + 3;
        if (d2 < min * min) {
          const d = Math.sqrt(d2), push = ((min - d) / d) * 0.25;
          p.vx -= dx * push; p.vy -= dy * push; o.vx += dx * push; o.vy += dy * push;
        }
      }
    }
    for (const [ia, ib] of L) {
      const s = N[ia], t = N[ib];
      let x = t.x + t.vx - s.x - s.vx, y = t.y + t.vy - s.y - s.vy;
      const l = Math.sqrt(x * x + y * y) || 1;
      const ca = linkCount[ia], cb = linkCount[ib];
      const k = ((l - (30 + s.r + t.r)) / l) * alpha / Math.min(ca, cb);
      x *= k; y *= k;
      const bias = ca / (ca + cb);
      t.vx -= x * bias; t.vy -= y * bias; s.vx += x * (1 - bias); s.vy += y * (1 - bias);
    }
    for (const p of V) {
      const c = centres[p.dom];
      p.vx += (c.x - p.x) * 0.05 * alpha; p.vy += (c.y - p.y) * 0.05 * alpha;
      if (p.fx !== null) { p.x = p.fx; p.y = p.fy; p.vx = p.vy = 0; continue; }
      p.vx *= 0.6; p.vy *= 0.6;
      p.x += p.vx; p.y += p.vy;
    }
  }

  const running = () => alpha >= ALPHA_MIN || alphaTarget > 0;

  // Settle most of the way before the first paint, so the page does not open
  // on a cloud of points.
  function settle(ms) {
    const end = performance.now() + ms;
    while (running() && performance.now() < end) tick();
  }

  // ------------------------------------------------------------ view
  let W = 0, H = 0, dpr = 1;
  const cam = {k: 1, x: 0, y: 0};
  let goal = null;     // camera target while it glides
  let autoFit = true;  // until the reader pans or zooms, the view follows the layout
  let follow = -1;     // or it follows one node, while the layout still moves it

  function resize() {
    const r = stage.getBoundingClientRect();
    dpr = window.devicePixelRatio || 1;
    W = r.width; H = r.height;
    canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr);
    if (autoFit) fit(false);
    draw();
  }

  // The width of the graph not covered by the selection card, which floats
  // over its right side on a wide screen.
  function openW() {
    if (panel.hidden || getComputedStyle(panel).position !== 'absolute') return W;
    return Math.max(W * 0.4, W - panel.offsetWidth - 24);
  }

  function fitTo(nodes, glide, maxK) {
    if (!nodes.length || !W) return;
    const ow = openW();
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (const n of nodes) {
      x0 = Math.min(x0, n.x - n.r); y0 = Math.min(y0, n.y - n.r);
      x1 = Math.max(x1, n.x + n.r); y1 = Math.max(y1, n.y + n.r);
    }
    const pad = 36;
    const k = Math.max(0.08, Math.min(maxK, (ow - 2 * pad) / Math.max(1, x1 - x0), (H - 2 * pad) / Math.max(1, y1 - y0)));
    const t = {k, x: ow / 2 - ((x0 + x1) / 2) * k, y: H / 2 - ((y0 + y1) / 2) * k};
    if (glide && !reduced) goal = t; else { Object.assign(cam, t); goal = null; }
  }
  const fit = glide => fitTo(V, glide, 2.2);

  function zoomAt(f, sx, sy) {
    const k = Math.max(0.05, Math.min(8, cam.k * f));
    cam.x = sx - ((sx - cam.x) / cam.k) * k;
    cam.y = sy - ((sy - cam.y) / cam.k) * k;
    cam.k = k;
    goal = null; autoFit = false; follow = -1;
    schedule();
  }

  function centreOn(n, k) {
    k = k || Math.max(cam.k, 1.3);
    const t = {k, x: openW() / 2 - n.x * k, y: H / 2 - n.y * k};
    if (reduced) Object.assign(cam, t); else goal = t;
    autoFit = false;
    follow = n.i;
  }

  // ------------------------------------------------------------ colours
  let C = {};
  function readColours() {
    const cs = getComputedStyle(document.documentElement);
    const v = name => cs.getPropertyValue(name).trim();
    C = {
      ink: v('--ink'), ink2: v('--ink-2'), ink3: v('--ink-3'), rule: v('--rule'),
      panel: v('--panel'), accent: v('--accent'), comm: v('--comm'),
      dom: D.domains.map(([, , slot]) => v('--g' + slot)),
      dark: matchMedia('(prefers-color-scheme: dark)').matches,
    };
  }

  // ------------------------------------------------------------ drawing
  let queued = false;
  function schedule() {
    if (!queued) { queued = true; requestAnimationFrame(frame); }
  }
  function frame() {
    queued = false;
    let more = false;
    if (running()) {
      tick(); tick();
      if (autoFit) fit(false);
      else if (follow >= 0 && visible[follow]) centreOn(N[follow], (goal || cam).k);
      more = true;
    }
    if (goal) {
      const f = 0.22;
      cam.k += (goal.k - cam.k) * f; cam.x += (goal.x - cam.x) * f; cam.y += (goal.y - cam.y) * f;
      if (Math.abs(goal.k - cam.k) < 1e-3 && Math.abs(goal.x - cam.x) < 0.5 && Math.abs(goal.y - cam.y) < 0.5) {
        Object.assign(cam, goal); goal = null;
      } else more = true;
    }
    draw();
    if (more) schedule();
  }

  const sx = n => n.x * cam.k + cam.x;
  const sy = n => n.y * cam.k + cam.y;

  function arrow(x0, y0, x1, y1, r, size) {
    const dx = x1 - x0, dy = y1 - y0, l = Math.hypot(dx, dy);
    if (l < r + size + 2) return;
    const ux = dx / l, uy = dy / l;
    const ex = x1 - ux * (r + 1.5), ey = y1 - uy * (r + 1.5);
    ctx.moveTo(ex, ey);
    ctx.lineTo(ex - ux * size - uy * size * 0.55, ey - uy * size + ux * size * 0.55);
    ctx.lineTo(ex - ux * size + uy * size * 0.55, ey - uy * size - ux * size * 0.55);
    ctx.closePath();
  }

  function draw() {
    if (!W) return;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);
    const k = cam.k;
    const focus = state.sel >= 0 && visible[state.sel] ? state.sel : hover;
    const near = new Set();
    if (focus >= 0) {
      near.add(focus);
      for (const j of N[focus].deps) near.add(j);
      for (const j of N[focus].users) near.add(j);
    }
    const dim = focus >= 0;

    // Edges: the quiet ones in one pass, the focused node's on top.
    ctx.lineWidth = 1;
    ctx.strokeStyle = C.ink3;
    ctx.fillStyle = C.ink3;
    ctx.globalAlpha = dim ? 0.08 : (C.dark ? 0.3 : 0.26);
    ctx.beginPath();
    for (const [a, b] of L) {
      if (dim && (a === focus || b === focus)) continue;
      ctx.moveTo(sx(N[a]), sy(N[a])); ctx.lineTo(sx(N[b]), sy(N[b]));
    }
    ctx.stroke();
    if (k > 0.9 && !dim) {
      ctx.beginPath();
      for (const [a, b] of L) arrow(sx(N[a]), sy(N[a]), sx(N[b]), sy(N[b]), N[b].r * k, 3 + k);
      ctx.fill();
    }
    ctx.globalAlpha = 1;
    if (dim) {
      const f = N[focus];
      for (const [list, colour, out] of [[f.deps, C.accent, true], [f.users, C.comm, false]]) {
        ctx.strokeStyle = colour; ctx.fillStyle = colour; ctx.lineWidth = 1.6;
        ctx.beginPath();
        for (const j of list) if (visible[j]) { ctx.moveTo(sx(f), sy(f)); ctx.lineTo(sx(N[j]), sy(N[j])); }
        ctx.stroke();
        ctx.beginPath();
        for (const j of list) {
          if (!visible[j]) continue;
          const [s, t] = out ? [f, N[j]] : [N[j], f];
          arrow(sx(s), sy(s), sx(t), sy(t), t.r * Math.max(k, 0.35), 5);
        }
        ctx.fill();
      }
    }

    // Nodes.
    for (const n of byR) {
      if (!visible[n.i]) continue;
      const x = sx(n), y = sy(n), r = Math.max(1.6, n.r * k);
      if (x < -r || y < -r || x > W + r || y > H + r) continue;
      ctx.globalAlpha = dim && !near.has(n.i) ? 0.18 : 1;
      const col = C.dom[n.dom];
      ctx.beginPath();
      if (n.def) {
        ctx.moveTo(x, y - r); ctx.lineTo(x + r, y); ctx.lineTo(x, y + r); ctx.lineTo(x - r, y); ctx.closePath();
        ctx.fillStyle = C.panel; ctx.fill();
        ctx.lineWidth = Math.max(1.2, Math.min(2.2, r * 0.35)); ctx.strokeStyle = col; ctx.stroke();
      } else {
        ctx.arc(x, y, r, 0, 2 * Math.PI);
        ctx.fillStyle = col; ctx.fill();
        if (r > 3) { ctx.lineWidth = 1.5; ctx.strokeStyle = C.panel; ctx.stroke(); }
      }
      if (n.i === state.sel) {
        ctx.beginPath(); ctx.arc(x, y, r + 4.5, 0, 2 * Math.PI);
        ctx.lineWidth = 2.5; ctx.strokeStyle = C.ink; ctx.stroke();
      } else if (n.i === hover) {
        ctx.beginPath(); ctx.arc(x, y, r + 3.5, 0, 2 * Math.PI);
        ctx.lineWidth = 1.5; ctx.strokeStyle = C.ink2; ctx.stroke();
      }
    }
    ctx.globalAlpha = 1;

    // Labels: the focus and its neighbours first, then the most-used nodes
    // that fit without colliding.
    ctx.font = '500 11px "JetBrains Mono", ui-monospace, monospace';
    ctx.textBaseline = 'middle';
    ctx.lineJoin = 'round';
    const boxes = [];
    const order = [];
    if (focus >= 0) { order.push(N[focus]); for (const j of near) if (j !== focus) order.push(N[j]); }
    for (let a = byR.length - 1; a >= 0; a--) {
      const n = byR[a];
      if (!near.has(n.i) && !dim && (n.users.length >= 3 || n.r * k >= 6.5 || k >= 1.7)) order.push(n);
    }
    let placed = 0;
    for (const n of order) {
      if (!visible[n.i] || placed > 220) continue;
      const gap = Math.max(1.6, n.r * k) + 5, w = ctx.measureText(n.label).width, y = sy(n);
      // A label that would run off the right edge goes on the node's left.
      let x = sx(n) + gap;
      if (x + w > W - 6) x = sx(n) - gap - w;
      if (x < 0 || x + w > W || y < 0 || y > H) continue;
      const b = [x - 2, y - 8, x + w + 2, y + 8];
      if (n.i !== focus && boxes.some(o => b[0] < o[2] && b[2] > o[0] && b[1] < o[3] && b[3] > o[1])) continue;
      boxes.push(b); placed++;
      ctx.lineWidth = 3.5; ctx.strokeStyle = C.panel; ctx.strokeText(n.label, x, y);
      ctx.fillStyle = n.i === focus ? C.ink : C.ink2; ctx.fillText(n.label, x, y);
    }
  }

  // ------------------------------------------------------------ pointer
  function pick(px, py) {
    let best = -1, bd = Infinity;
    for (const n of V) {
      const d = Math.hypot(sx(n) - px, sy(n) - py), lim = Math.max(6, n.r * cam.k + 3);
      if (d <= lim && d < bd) { bd = d; best = n.i; }
    }
    return best;
  }
  const local = ev => { const r = canvas.getBoundingClientRect(); return [ev.clientX - r.left, ev.clientY - r.top]; };

  const ptrs = new Map();
  let drag = null, pan = null, pinch = null;

  canvas.addEventListener('pointerdown', ev => {
    canvas.setPointerCapture(ev.pointerId);
    const [x, y] = local(ev);
    ptrs.set(ev.pointerId, [x, y]);
    hideTip();
    if (ptrs.size === 2) {
      const [[ax, ay], [bx, by]] = [...ptrs.values()];
      pinch = {d: Math.hypot(ax - bx, ay - by) || 1, k: cam.k, cx: cam.x, cy: cam.y, mx: (ax + bx) / 2, my: (ay + by) / 2};
      if (drag) { N[drag.i].fx = N[drag.i].fy = null; alphaTarget = 0; }
      drag = pan = null;
      return;
    }
    const i = pick(x, y);
    if (i >= 0) drag = {i, x, y, moved: false};
    else pan = {x, y, cx: cam.x, cy: cam.y, moved: false};
    canvas.classList.add('drag');
  });

  canvas.addEventListener('pointermove', ev => {
    const [x, y] = local(ev);
    if (ptrs.has(ev.pointerId)) ptrs.set(ev.pointerId, [x, y]);
    if (pinch && ptrs.size === 2) {
      const [[ax, ay], [bx, by]] = [...ptrs.values()];
      const k = Math.max(0.05, Math.min(8, pinch.k * Math.hypot(ax - bx, ay - by) / pinch.d));
      const mx = (ax + bx) / 2, my = (ay + by) / 2;
      cam.x = mx - ((pinch.mx - pinch.cx) / pinch.k) * k;
      cam.y = my - ((pinch.my - pinch.cy) / pinch.k) * k;
      cam.k = k; goal = null; autoFit = false; follow = -1;
      schedule();
      return;
    }
    if (drag) {
      if (!drag.moved && Math.hypot(x - drag.x, y - drag.y) < 4) return;
      drag.moved = true;
      const n = N[drag.i];
      n.fx = (x - cam.x) / cam.k; n.fy = (y - cam.y) / cam.k;
      alphaTarget = 0.25; autoFit = false; follow = -1;
      schedule();
      return;
    }
    if (pan) {
      if (!pan.moved && Math.hypot(x - pan.x, y - pan.y) < 4) return;
      pan.moved = true;
      cam.x = pan.cx + x - pan.x; cam.y = pan.cy + y - pan.y;
      goal = null; autoFit = false; follow = -1;
      schedule();
      return;
    }
    if (ev.pointerType === 'mouse') {
      const i = pick(x, y);
      if (i !== hover) { hover = i; canvas.classList.toggle('over', i >= 0); schedule(); }
      if (i >= 0) showTip(N[i], x, y); else hideTip();
    }
  });

  function release(ev) {
    ptrs.delete(ev.pointerId);
    canvas.classList.remove('drag');
    if (pinch) { if (ptrs.size < 2) pinch = null; return; }
    if (drag) {
      const n = N[drag.i];
      if (drag.moved) { n.fx = n.fy = null; alphaTarget = 0; schedule(); }
      else if (ev.type === 'pointerup') select(drag.i, false);
      drag = null;
    }
    if (pan) {
      if (!pan.moved && ev.type === 'pointerup') select(-1, false);
      pan = null;
    }
  }
  canvas.addEventListener('pointerup', release);
  canvas.addEventListener('pointercancel', release);
  canvas.addEventListener('pointerleave', ev => {
    if (ev.pointerType === 'mouse' && hover >= 0) { hover = -1; canvas.classList.remove('over'); hideTip(); schedule(); }
  });
  canvas.addEventListener('dblclick', ev => {
    const [x, y] = local(ev);
    const i = pick(x, y);
    if (i >= 0) location.href = `${root}d/${N[i].slug}/`;
  });
  canvas.addEventListener('wheel', ev => {
    ev.preventDefault();
    const [x, y] = local(ev);
    const unit = ev.deltaMode === 1 ? 32 : ev.deltaMode === 2 ? H : 1;
    zoomAt(Math.exp(-ev.deltaY * unit * (ev.ctrlKey ? 0.01 : 0.0018)), x, y);
  }, {passive: false});

  document.getElementById('g-close').addEventListener('click', () => select(-1, false));

  for (const b of document.querySelectorAll('.g-zoom button')) {
    b.addEventListener('click', () => {
      const z = b.dataset.zoom;
      if (z === 'fit') { autoFit = true; follow = -1; fit(true); schedule(); }
      else zoomAt(z === 'in' ? 1.4 : 1 / 1.4, W / 2, H / 2);
    });
  }

  function showTip(n, x, y) {
    tip.innerHTML = '';
    const t = document.createElement('span'); t.className = 't';
    t.textContent = `${D.domains[n.dom][1]} · ${n.topic}`;
    const nm = document.createElement('span'); nm.className = 'n'; nm.textContent = n.name;
    tip.append(t, nm);
    if (n.words) tip.append(document.createTextNode(n.words.length > 150 ? n.words.slice(0, 149) + '…' : n.words));
    tip.hidden = false;
    const tw = tip.offsetWidth, th = tip.offsetHeight;
    tip.style.left = Math.min(W - tw - 8, x + 14) + 'px';
    tip.style.top = (y + th + 20 > H ? y - th - 12 : y + 14) + 'px';
  }
  function hideTip() { tip.hidden = true; }

  // ------------------------------------------------------------ selection
  function el(tag, cls, text) {
    const x = document.createElement(tag);
    if (cls) x.className = cls;
    if (text !== undefined) x.textContent = text;
    return x;
  }

  function nodeList(title, idx, colour) {
    const box = el('div', 'g-list');
    const h = el('h3', '', `${title} (${idx.length})`);
    h.style.boxShadow = `inset 3px 0 0 ${colour}`;
    h.style.paddingLeft = '8px';
    box.append(h);
    if (!idx.length) { box.append(el('p', 'none', 'nothing in the knowledgebase')); return box; }
    const ul = el('ul');
    const sorted = [...idx].sort((a, b) => N[b].users.length - N[a].users.length || (N[a].name < N[b].name ? -1 : 1));
    for (const j of sorted.slice(0, 40)) {
      const m = N[j];
      const b = el('button');
      b.type = 'button';
      b.title = m.words ? `${m.name}\n${m.words}` : m.name;
      const sw = el('span', 'sw' + (m.def ? ' def' : ''));
      sw.style.background = `var(--g${D.domains[m.dom][2]})`;
      b.append(sw, el('span', 'nm', m.name));
      b.addEventListener('click', () => select(j, true));
      const li = el('li'); li.append(b); ul.append(li);
    }
    box.append(ul);
    if (sorted.length > 40) box.append(el('p', 'more', `and ${sorted.length - 40} more on its page`));
    return box;
  }

  function renderPanel() {
    if (state.sel < 0) { panel.hidden = true; selBox.innerHTML = ''; return; }
    const n = N[state.sel];
    panel.hidden = false; selBox.innerHTML = '';
    const where = el('p', 'g-where');
    const sw = el('span', 'sw'); sw.style.background = `var(--g${D.domains[n.dom][2]})`;
    where.append(sw, document.createTextNode(`${D.domains[n.dom][1]} · ${n.topic} · ${n.def ? 'definition' : 'theorem'}`));
    const h = el('h2', 'g-name');
    const a = el('a', '', n.name); a.href = `${root}d/${n.slug}/`;
    h.append(a);
    selBox.append(where, h);
    if (n.words) selBox.append(el('p', 'prose', n.words));
    const acts = el('div', 'g-acts');
    const open = el('a', 'btn primary', n.def ? 'Open the definition' : 'Open the proof');
    open.href = `${root}d/${n.slug}/`;
    const chain = el('button', 'btn', state.chain ? 'Show everything' : 'Only its chain');
    chain.type = 'button';
    chain.title = 'Show only what it builds on, directly or not, and what builds on it';
    chain.setAttribute('aria-pressed', String(state.chain));
    chain.addEventListener('click', () => { state.chain = !state.chain; refilter(); renderPanel(); });
    acts.append(open, chain);
    selBox.append(acts);
    selBox.append(nodeList('Builds on', n.deps, C.accent), nodeList('Used by', n.users, C.comm));
  }

  function select(i, centre) {
    const prev = state.sel;
    state.sel = i;
    if (i < 0) follow = -1;
    if (i >= 0) {
      const n = N[i];
      // Whatever hides the chosen node gives way to it.
      if (n.def && !state.defs) { state.defs = true; syncControls(); }
      if (state.off.has(n.dom)) { state.off.delete(n.dom); syncControls(); }
    }
    if (state.chain && i !== prev) {
      if (i < 0) state.chain = false;
      refilter();
    } else if (i >= 0 && !visible[i]) refilter();
    renderPanel();
    writeUrl();
    // With the chain on, the view refits to the new chain instead.
    if (i >= 0 && centre && !state.chain) centreOn(N[i]);
    schedule();
  }

  // ------------------------------------------------------------ controls
  const segs = [...document.querySelectorAll('[data-defs]')];
  const legend = [...document.querySelectorAll('.g-dom')];

  function syncControls() {
    for (const b of segs) b.setAttribute('aria-pressed', String((b.dataset.defs === '1') === state.defs));
    for (const b of legend) b.setAttribute('aria-pressed', String(!state.off.has(+b.dataset.dom)));
    const per = new Map();
    for (const n of N) if (state.defs || !n.def) per.set(n.dom, (per.get(n.dom) || 0) + 1);
    for (const c of document.querySelectorAll('[data-dom-count]')) c.textContent = per.get(+c.dataset.domCount) || 0;
  }

  function updateCount() {
    const all = state.defs || cone;
    const total = all ? N.length : N.filter(n => !n.def).length;
    const what = all ? 'declarations' : 'theorems';
    countEl.textContent = (V.length === total ? `${total} ${what}` : `${V.length} of ${total} ${what}`)
      + ` · ${L.length} uses`;
  }

  function refilter() {
    if (state.sel >= 0 && !(state.defs || !N[state.sel].def)) state.sel = -1;
    if (state.sel >= 0 && state.off.has(N[state.sel].dom)) state.sel = -1;
    if (state.sel < 0) state.chain = false;
    relayout(0.7);
    if (reduced) settle(800);
    autoFit = true; follow = -1;
    hover = -1;
    renderPanel();
    writeUrl();
    schedule();
  }

  for (const b of segs) b.addEventListener('click', () => {
    const v = b.dataset.defs === '1';
    if (v === state.defs) return;
    state.defs = v; syncControls(); refilter();
  });
  for (const b of legend) b.addEventListener('click', () => {
    const d = +b.dataset.dom;
    if (state.off.has(d)) state.off.delete(d); else state.off.add(d);
    syncControls(); refilter();
  });

  // ------------------------------------------------------------ search
  let found = [], cursor = -1;
  function search() {
    const words = norm(q.value).split(' ').filter(Boolean);
    found = [];
    if (words.length) {
      const name = norm(q.value);
      found = N.filter(n => words.every(w => n.hay.includes(w)))
        .sort((a, b) => (norm(b.name).startsWith(name) - norm(a.name).startsWith(name))
          || (a.def - b.def) || (b.users.length - a.users.length))
        .slice(0, 10);
    }
    cursor = found.length ? 0 : -1;
    paintHits();
  }
  function paintHits() {
    hits.innerHTML = '';
    if (!q.value.trim()) { hits.hidden = true; q.setAttribute('aria-expanded', 'false'); return; }
    if (!found.length) {
      hits.append(el('li', 'none', 'Nothing matches.'));
    }
    found.forEach((n, k) => {
      const li = el('li');
      li.setAttribute('role', 'option');
      li.setAttribute('aria-selected', String(k === cursor));
      li.append(el('span', 'n', n.name), el('span', 'w', n.words || n.topic));
      li.addEventListener('mousedown', ev => { ev.preventDefault(); choose(n); });
      hits.append(li);
    });
    hits.hidden = false;
    q.setAttribute('aria-expanded', 'true');
  }
  function choose(n) {
    q.value = '';
    found = []; paintHits();
    select(n.i, true);
  }
  q.addEventListener('input', search);
  q.addEventListener('keydown', ev => {
    if (ev.key === 'ArrowDown' || ev.key === 'ArrowUp') {
      if (!found.length) return;
      ev.preventDefault();
      cursor = (cursor + (ev.key === 'ArrowDown' ? 1 : found.length - 1)) % found.length;
      paintHits();
    } else if (ev.key === 'Enter') {
      if (cursor >= 0) { ev.preventDefault(); choose(found[cursor]); }
    } else if (ev.key === 'Escape') {
      q.value = ''; found = []; paintHits();
    }
  });
  q.addEventListener('blur', () => { hits.hidden = true; q.setAttribute('aria-expanded', 'false'); });
  q.addEventListener('focus', () => { if (q.value.trim()) paintHits(); });

  document.addEventListener('keydown', ev => {
    const t = ev.target;
    if (t.closest && t.closest('input, textarea, select, [contenteditable]')) return;
    if (ev.key === 'Escape' && state.sel >= 0) select(-1, false);
  });

  // ------------------------------------------------------------ address
  // ?n=<name> selects a declaration (the declaration pages link here that
  // way); defs=1 and chain=1 restore the two switches. The list's filters
  // share the query string, so only these three keys are touched.
  function writeUrl() {
    const p = new URLSearchParams(location.search);
    const set = (k, v) => { if (v) p.set(k, v); else p.delete(k); };
    set('n', state.sel >= 0 ? N[state.sel].name : '');
    set('defs', state.defs ? '1' : '');
    set('chain', state.chain ? '1' : '');
    const s = p.toString();
    try { history.replaceState(null, '', (s ? '?' + s : location.pathname) + location.hash); } catch (_) {}
  }

  const p = new URLSearchParams(location.search);
  state.defs = p.get('defs') === '1';
  const want = N.find(n => n.name === p.get('n'));
  if (want) {
    state.sel = want.i;
    if (want.def) state.defs = true;
    state.chain = p.get('chain') === '1';
  }

  readColours();
  const scheme = matchMedia('(prefers-color-scheme: dark)');
  const recolour = () => { readColours(); renderPanel(); schedule(); };
  if (scheme.addEventListener) scheme.addEventListener('change', recolour);

  syncControls();
  relayout(1);
  settle(reduced ? 1500 : 260);
  if ('ResizeObserver' in window) new ResizeObserver(resize).observe(stage);
  else window.addEventListener('resize', resize);
  resize();
  renderPanel();
  if (want && !state.chain) centreOn(want);
  schedule();
})();
