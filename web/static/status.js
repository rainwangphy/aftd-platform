// The status page: reads the file the scheduler lane pushes every few minutes
// (aftd/status.py) and draws the day as lanes in time, 20:00 to 20:00: what
// each lane has done since the last release, and what it is doing now.
(function () {
  const box = document.getElementById("st");
  if (!box) return;
  const src = box.dataset.src;
  const STALE = 30 * 60; // seconds without an update before the lights go grey
  const DAY = 1440;      // minutes in the day's window
  const esc = (t) => String(t).replace(/[&<>"]/g, (c) => ({"&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;"}[c]));
  const ago = (s) => s < 90 ? "just now" : s < 5400 ? Math.round(s / 60) + " min ago" : Math.round(s / 3600) + " h ago";
  const pct = (m) => (Math.max(0, Math.min(DAY, m)) / DAY * 100).toFixed(3) + "%";
  const WORD = {working: "working", waiting: "waiting", stopped: "stopped", off: "off", unknown: "no news"};
  const date = (start, m, opts) => new Date((start + m * 60) * 1000)
    .toLocaleDateString("en-GB", Object.assign({timeZone: "Asia/Shanghai"}, opts));
  const clock = (start, m) => {
    const d = new Date((start + m * 60) * 1000);
    return d.toLocaleTimeString("en-GB", {hour: "2-digit", minute: "2-digit", timeZone: "Asia/Shanghai"});
  };

  function axis(d) {
    let ticks = "";
    for (let h = 0; h <= 24; h += 2) {
      const m = h * 60, ends = h === 0 || h === 24;
      const label = (ends ? date(d.start, m, {day: "numeric", month: "short"}) + " " : "") + clock(d.start, m);
      ticks += `<span class="ln-tick${h % 4 ? " odd" : ""}${ends ? " end" : ""}" style="left:${pct(m)}">${label}</span>`;
    }
    return `<div class="ln-row ln-axis" aria-hidden="true"><div class="ln-head"></div>
      <div class="ln-track ln-ticks">${ticks}</div></div>`;
  }

  function track(segs, now, extra) {
    const bars = (segs || []).map(([a, b, st]) =>
      `<span class="ln-seg ${st}" style="left:${pct(a)};width:${pct(b - a)}" title="${WORD[st] || st}"></span>`).join("");
    return `<div class="ln-track">${extra || ""}${bars}
      <span class="ln-future" style="left:${pct(now)};width:${pct(DAY - now)}"></span>
      <span class="ln-now" style="left:${pct(now)}"></span></div>`;
  }

  function draw(d) {
    const nowS = Date.now() / 1000, age = nowS - d.generated, stale = age > STALE;
    const now = d.now_min;
    document.getElementById("st-upd").innerHTML = stale
      ? `<strong>No update for ${ago(age).replace(" ago", "")}</strong>: the lanes show the last known state.`
      : `Updated ${ago(age)} &middot; the day runs from ${clock(d.start, 0)} to ${clock(d.start, DAY)}, ${esc(d.timezone)}, when it is released`;
    const rows = d.lanes.map((l) => {
      const st = stale ? "unknown" : l.state;
      let extra = "";
      if (l.id === "frontier" && d.cc_hours && d.cc_hours.length === 2 && d.cc_hours[1] > now) {
        const a = Math.max(now, d.cc_hours[0]);
        extra = `<span class="ln-plan" style="left:${pct(a)};width:${pct(d.cc_hours[1] - a)}" title="its hours"></span>`;
      }
      return `<div class="ln-row st-${st}">
        <div class="ln-head"><p class="ln-name"><i class="dot ${st}"></i>${esc(l.name)}
          <span class="st-word">${WORD[st] || st}</span></p>
          <p class="ln-doing">${esc(l.doing)}</p>
          <p class="ln-role small">${esc(l.role)}</p></div>
        ${track(l.track, now, extra)}</div>`;
    });
    // Under each mark its time; a mark close to the one before drops its time
    // to a second line, so labels never overlap.
    let prev = -1e9, low = false;
    const marks = (d.events || []).slice().sort((a, b) => a.min - b.min).map((e) => {
      low = e.min - prev < 150 ? !low : false;
      prev = e.min;
      const kind = e.label === "release" ? "rel" : "read";
      return `<span class="ln-mark ${e.kind === "next" ? "next" : "done"} ${kind}${low ? " low" : ""}${e.min >= DAY ? " last" : ""}${e.min < 30 ? " first" : ""}"
        style="left:${pct(e.min)}" title="${esc(e.label)} at ${clock(d.start, e.min)}"><b>${clock(d.start, e.min)}</b></span>`;
    }).join("");
    const sched = `<div class="ln-row ln-sched"><div class="ln-head"><p class="ln-name">Readings and release</p>
      <p class="ln-role small"><i class="ln-key read"></i> reading, <i class="ln-key rel"></i> release;
      filled when done. The day's new papers are read at ${(d.schedule || []).filter((x) => x.what.startsWith("Reading")).map((x) => x.at).join(" and ")};
      the day is released at ${esc(d.release_at)}, waiting for no lane.</p></div>
      <div class="ln-track ln-marks">${marks}<span class="ln-now" style="left:${pct(now)}"></span></div></div>`;
    document.getElementById("st-lanes").innerHTML = axis(d) + rows.join("") + sched;
    document.getElementById("st-day").textContent = "· " +
      new Date(d.day + "T12:00:00+08:00").toLocaleDateString("en-GB",
        {weekday: "long", day: "numeric", month: "long", year: "numeric", timeZone: "Asia/Shanghai"});
    const t = d.today || {};
    document.getElementById("st-today").innerHTML =
      `Since the last release: <b>${t.proved ?? 0}</b> statements proved, <b>${t.stated ?? 0}</b> new statements in Lean,
       <b>${t.problems ?? 0}</b> open problems and <b>${t.results ?? 0}</b> results read from new papers;
       <b>${t.handed_up ?? 0}</b> tasks handed up to the frontier agent, <b>${t.closed ?? 0}</b> closed by it,
       <b>${t.inbox_waiting ?? 0}</b> waiting in its inbox.`;
  }

  function load() {
    fetch(src + "?t=" + Math.floor(Date.now() / 60000), {cache: "no-store"})
      .then((r) => (r.ok ? r.json() : Promise.reject(r.status)))
      .then(draw)
      .catch(() => {
        document.getElementById("st-upd").textContent = "The status file could not be read just now; trying again shortly.";
      });
  }
  load();
  setInterval(load, 3 * 60 * 1000);
})();
