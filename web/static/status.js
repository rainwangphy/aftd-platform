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
    // Dates on a line of their own, each where its day begins; times below.
    const mid = (24 - new Date((d.start) * 1000).getUTCHours() - 8 + 48) % 24 * 60; // minutes to midnight, UTC+8
    const dates = [[0, d.start], [mid, d.start + mid * 60]].filter(([m]) => m < DAY - 60).map(([m]) =>
      `<span class="ln-date${m ? "" : " first"}" style="left:${pct(m)}">${date(d.start, m, {weekday: "short", day: "numeric", month: "short"})}</span>`).join("");
    let ticks = "";
    for (let h = 0; h <= 24; h += 2) {
      ticks += `<span class="ln-tick${h % 4 ? " odd" : ""}" style="left:${pct(h * 60)}">${clock(d.start, h * 60)}</span>`;
    }
    return `<div class="ln-row ln-axis" aria-hidden="true"><div class="ln-head"></div>
      <div class="ln-axis-in"><div class="ln-track ln-dates">${dates}</div>
      <div class="ln-track ln-ticks">${ticks}</div></div></div>`;
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
        <div class="ln-head" title="${esc(l.role)}"><p class="ln-name"><i class="dot ${st}"></i>${esc(l.name)}
          <span class="ln-doing">${esc(l.doing)}</span></p></div>
        ${track(l.track, now, extra)}</div>`;
    });
    // Under each mark its time; a mark close to the one before drops its time
    // to a second line, so labels never overlap.
    // Marks, no words: hollow before a run, solid where it began, and where it
    // ended solid (succeeded) or red (failed); a bar joins the two, or runs to
    // now while it goes. A run killed, or a reading whose time passed unbegun,
    // is red where it should have been.
    const pts = [], bars = [];
    for (const e of d.events || []) {
      const kind = e.label === "release" ? "rel" : "read";
      const st = e.kind === "next" ? "next" : (e.state || "done");
      if (st === "next") { pts.push({min: e.min, kind, cls: "next", what: "due"}); continue; }
      if (st === "late") { pts.push({min: e.min, kind, cls: "next bad", what: "not begun"}); continue; }
      // An end not logged (older logs): a failure is marked where it began.
      const badStart = st === "stopped" || (st === "failed" && e.end == null);
      pts.push({min: e.min, kind, cls: badStart ? "done bad" : "done", what: badStart ? "failed" : "began"});
      if (e.end != null) pts.push({min: e.end, kind, cls: st === "failed" ? "done bad" : "done",
                                   what: st === "failed" ? "ended with an error" : "finished"});
      const until = e.end != null ? e.end : st === "running" ? now : null;
      if (until != null && until > e.min) bars.push(
        `<span class="ln-run ${kind}${st === "running" ? " running" : ""}" style="left:${pct(e.min)};width:calc(${pct(until)} - ${pct(e.min)})"></span>`);
    }
    // Times under the marks on two lines; a mark too close to both labels
    // before it keeps its time in the tooltip only.
    const last = [-1e9, -1e9];  // the last label on the top line, on the low one
    const marks = bars.join("") + pts.sort((a, b) => a.min - b.min).map((p) => {
      const at = clock(d.start, p.min);
      const line = p.min - last[0] >= 75 ? 0 : p.min - last[1] >= 75 ? 1 : -1;
      if (line >= 0) last[line] = p.min;
      return `<span class="ln-mark ${p.cls} ${p.kind}${line === 1 ? " low" : ""}${p.min >= DAY ? " last" : ""}${p.min < 30 ? " first" : ""}"
        style="left:${pct(p.min)}" title="${p.kind === "rel" ? "release" : "reading"} ${p.what} at ${at}">${line >= 0 ? `<b>${at}</b>` : ""}</span>`;
    }).join("");
    const sched = `<div class="ln-row ln-sched"><div class="ln-head"><p class="ln-name">Schedule
      <span class="ln-doing"><i class="ln-key read"></i>reading <i class="ln-key rel"></i>release</span></p></div>
      <div class="ln-track ln-marks">${marks}<span class="ln-now" style="left:${pct(now)}"></span></div></div>`;
    document.getElementById("st-lanes").innerHTML = axis(d) + rows.join("") + sched;
    document.getElementById("st-day").textContent = "· " +
      new Date(d.day + "T12:00:00+08:00").toLocaleDateString("en-GB",
        {weekday: "long", day: "numeric", month: "long", year: "numeric", timeZone: "Asia/Shanghai"});
    const t = d.today || {};
    // Since the release, as cards: one number each, read at a glance.
    const card = (n, k, cls, sub) => `<div class="st-card ${cls}"><span class="v">${n ?? 0}</span>
      <span class="k">${k}</span>${sub ? `<span class="s">${sub}</span>` : ""}</div>`;
    document.getElementById("st-today").innerHTML =
      `<p class="st-cap">Since the last release</p><div class="st-cards">
       ${card(t.proved, "statements proved", "proved")}
       ${card(t.stated, "stated in Lean", "stated")}
       ${card(t.research, "research-level results", "research")}
       ${card(t.posed, "questions posed", "stated")}
       ${card(t.problems, "open problems listed", "read")}
       ${card(t.results, "results read", "read")}
       ${card(t.handed_up, "sent to frontier", "up", `<b>${t.closed ?? 0}</b> closed`)}
       ${card(t.inbox_waiting, "in frontier inbox", t.inbox_waiting ? "wait" : "")}</div>`;
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
