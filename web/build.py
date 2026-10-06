#!/usr/bin/env python3
"""Build the public AFTD site from the knowledgebase snapshot and the issues.

    python3 web/build.py --out _site

Inputs, all under `web/`:

* `data/kb.json` -- written by `scripts/snapshot.py` on the machine that runs
  the loop, and committed. Every declaration the site shows comes from here.
* `data/problems.json` -- written by `fetch_problems.py` from GitHub issues at
  build time. Optional: without it the site simply has no community problems.
* `site.json` -- the repository and branch that every outbound link points at.
* `news.json` -- announcements, written by hand: launches and newly proved
  results. A proof announcement must name only declarations Lean verified, or
  the build stops.
* `weekly/<week>.json`, `monthly/<month>.json` -- the summary reports
  (`aftd interpret --week` / `--month`): what
  Lean accepted that week, in words. Same rule: every declaration a report
  names must be verified, or the build stops.

Pages:

    index.html                  what this is, what is new (the News section),
                                where to start
    knowledgebase/              every verified declaration: first as a dependency
                                graph (one node per declaration, one arrow per
                                use), then as a searchable list
    results/                    the page's old address, forwarding to the new one
    d/<name>/                   one declaration: statement, proof, dependencies,
                                the problem it answers, challenges against it
    problems/                   community problems by status, what is open, and
                                how to submit a problem or challenge a result
    problems/<number>/          one reviewed problem and what answers it
    news/                       the address the news first had, forwarding to the
                                home page's News section
    chat/                       chat with knowledgebase (experimental), opened
                                from the button beside the dependency graph: a chat that
                                runs in the browser on the reader's own API key,
                                reading chat/kb-index.json and chat/kb-detail.json
    reports/                    the summary reports, weekly and monthly, newest
                                first, tagged by period, with search and filters
    weekly/<week>/              one week: what was settled, what is open
    monthly/<month>/            one month, laid out the same way
    weekly/                     the old address of the reports, forwarding to
                                reports/
    submit/                     the old address of the submission guide,
                                forwarding to problems/#submit

Stdlib only, so CI needs nothing but Python. Everything a submitter wrote is
escaped; nothing unreviewed is published beyond a count.
"""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
import sys
import time
from pathlib import Path
from urllib.parse import quote, urlencode

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from problems import PROBLEM_LABEL, STATUS_TITLES, STATUSES, VERDICT_LABEL, status  # noqa: E402
import literature  # noqa: E402

e = html.escape
_SAFE_NAME = re.compile(r"^[A-Za-z0-9_]+$")

KATEX = "https://cdn.jsdelivr.net/npm/katex@0.16.11/dist"
FONTS = (
    "https://fonts.googleapis.com/css2?family=Archivo:wght@400;500;600;700"
    "&family=JetBrains+Mono:wght@400;500;700"
    "&family=Source+Serif+4:opsz,wght@8..60,400;8..60,600&display=swap"
)


# -------------------------------------------------------------------- model
class Site:
    """Everything the pages are rendered from, with the joins done once."""

    def __init__(
        self,
        kb: dict,
        issues: list[dict],
        cfg: dict,
        news: list[dict] | None = None,
        weekly: list[dict] | None = None,
        monthly: list[dict] | None = None,
    ):
        self.kb = kb
        self.cfg = cfg
        self.repo = cfg["repo"]
        self.branch = cfg.get("branch", "master")
        self.gh = f"https://github.com/{self.repo}"
        self.decls = kb["declarations"]
        self.by_name = {d["name"]: d for d in self.decls}
        self.open = kb.get("open") or []
        self.domains = {d["name"]: d for d in kb["domains"]}
        self.topics = {t["name"]: t for d in kb["domains"] for t in d["topics"]}
        self.grants = {g["id"]: g for g in kb.get("grants") or []}
        self.literature = kb.get("literature") or []

        self.problems = [i for i in issues if i["kind"] == PROBLEM_LABEL]
        self.verdicts = [i for i in issues if i["kind"] == VERDICT_LABEL]
        answers: dict[int, list[dict]] = {}
        for n in self.decls + self.open:
            if n.get("problem") is not None:
                answers.setdefault(n["problem"], []).append(n)
        self.answers = answers
        for p in self.problems:
            p["status"] = status(p, answers.get(p["number"], []))
        self.problem_by_number = {p["number"]: p for p in self.problems}
        self.challenges: dict[str, list[dict]] = {}
        for v in self.verdicts:
            name = v["fields"].get("declaration", "").strip().strip("`")
            if name in self.by_name:
                self.challenges.setdefault(name, []).append(v)
        # Each topic's declarations in the order the knowledgebase page lists them,
        # for the previous/next links on a declaration page.
        self.in_topic: dict[str, list[dict]] = {}
        for d in self.decls:
            self.in_topic.setdefault(d["topic"], []).append(d)
        self.weekly = check_weekly(self, weekly or [])
        self.monthly = check_weekly(self, monthly or [], "month")
        self.news = check_news(self, news or [])

    def reports(self, period: str) -> list[dict]:
        return self.monthly if period == "month" else self.weekly

    def verified(self, d: dict) -> bool:
        """Whether a theorem's axioms are all trusted. An empty list is the
        cleanest case -- Lean said it depends on no axioms at all -- although
        the snapshot's `clean` flag counts it as not clean."""
        return not d["is_def"] and all(a in self.kb["trusted_axioms"] for a in d["axioms"])

    # Outbound links. GitHub pre-fills an issue form from query parameters
    # named after the form's field ids.
    def new_problem(self) -> str:
        return f"{self.gh}/issues/new?template=problem.yml"

    def new_verdict(self, name: str = "") -> str:
        if not name:
            return f"{self.gh}/issues/new?template=verdict.yml"
        q = urlencode(
            {"template": "verdict.yml", "title": f"[Verdict] {name}", "declaration": name}
        )
        return f"{self.gh}/issues/new?{q}"

    def discussions(self, query: str = "") -> str:
        base = f"{self.gh}/discussions"
        return f"{base}?discussions_q={quote(query)}" if query else base

    def blob(self, path: str) -> str:
        return f"{self.gh}/blob/{self.branch}/{path}"

    def pending_url(self) -> str:
        q = "is:issue is:open label:problem -label:accepted -label:declined"
        return f"{self.gh}/issues?q={quote(q)}"

    def domain_title(self, name: str) -> str:
        d = self.domains.get(name)
        return d["title"] if d else (name or "Other")

    def topic_title(self, name: str) -> str:
        t = self.topics.get(name)
        return t["title"] if t else name


NEWS_KINDS = {
    "launch": "Launch",
    "proof": "Proved",
    "daily": "Daily reading",
    "weekly": "Weekly report",
    "monthly": "Monthly report",
}
_WEEK = re.compile(r"^\d{4}-W\d{2}$")
_MONTH = re.compile(r"^\d{4}-(0[1-9]|1[0-2])$")
# What a weekly and a monthly report differ in, on the site. A report's label
# is stored under "week" for both (2026-W40, 2026-10).
PERIODS = {
    "week": {"dir": "weekly", "tag": "Weekly", "noun": "week", "label": _WEEK,
             "format": "YYYY-Www", "news": "weekly", "key": "week"},
    "month": {"dir": "monthly", "tag": "Monthly", "noun": "month", "label": _MONTH,
              "format": "YYYY-MM", "news": "monthly", "key": "month"},
}
_DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def check_news_provenance(s: Site, where: str, n: dict, names: list[str]) -> None:
    """A proof announcement must not pass off someone else's result as ours: if
    every theorem it names formalizes a published one, it has to say so, and an
    erratum has to say that it is one. (Most entries mix the paper's results
    with new ones; the result pages label each declaration.)"""
    text = f'{n["title"]} {n["body"]}'
    provs = {s.by_name[x].get("provenance") for x in names
             if not s.by_name[x]["is_def"]} - {"lemma"}
    if provs == {"literature"} and not re.search(r"formali[sz]", text, re.I):
        raise ValueError(f"{where}: every theorem it names formalizes a published "
                         "result; the entry must say it is a formalization")
    if "erratum" in provs and not re.search(r"erratum|errata|correct|false|fail|wrong", text, re.I):
        raise ValueError(f"{where}: it names an erratum; the entry must say that a "
                         "published claim fails, and which")


def check_news(s: Site, entries: list[dict]) -> list[dict]:
    """The announcements, newest first, each with the anchor it is linked by.

    A mistake here is the operator's, not a submitter's, so it stops the
    build instead of being skipped: a proof announced for a declaration Lean
    has not verified is exactly what the site exists not to publish."""
    out, seen = [], set()
    for i, n in enumerate(entries):
        where = f"news.json entry {i + 1} ({n.get('title', '?')!r})"
        if not _DATE.match(n.get("date", "")):
            raise ValueError(f"{where}: date must be YYYY-MM-DD, not {n.get('date')!r}")
        time.strptime(n["date"], "%Y-%m-%d")
        if n.get("kind") not in NEWS_KINDS:
            raise ValueError(f"{where}: kind must be one of {sorted(NEWS_KINDS)}")
        if not (n.get("title") or "").strip() or not (n.get("body") or "").strip():
            raise ValueError(f"{where}: needs a title and a body")
        names = n.get("declarations") or []
        unknown = [x for x in names if x not in s.by_name]
        if unknown:
            raise ValueError(f"{where}: not in the knowledgebase: {', '.join(unknown)}")
        if n["kind"] == "proof" and not names:
            raise ValueError(f"{where}: a proof announcement must name its declarations")
        if n["kind"] in ("proof", "daily"):
            # A daily entry lists what it proved: the same standard applies.
            unverified = [x for x in names if not s.verified(s.by_name[x])]
            if unverified:
                raise ValueError(f"{where}: not a verified theorem: {', '.join(unverified)}")
        if n["kind"] == "proof":
            check_news_provenance(s, where, n, names)
        for period, P in PERIODS.items():
            if n["kind"] == P["news"] and n.get(P["key"]) not in {r["week"] for r in s.reports(period)}:
                raise ValueError(f"{where}: no {P['news']} report for {n.get(P['key'])!r} "
                                 f"in {P['dir']}/")
        nid = "n-" + n["date"] + "-" + (re.sub(r"[^a-z0-9]+", "-", n["title"].lower()).strip("-")[:48] or "x")
        if nid in seen:
            raise ValueError(f"{where}: two entries on the same day share a title")
        seen.add(nid)
        out.append({**n, "id": nid, "declarations": names, "links": n.get("links") or []})
    # Newest first; entries of the same day keep the file's order.
    return sorted(out, key=lambda n: n["date"], reverse=True)


WEEKLY_FORMAT = 2
WEEKLY_OUTCOMES = ("proved", "disproved", "partial", "new", "formalized")


def check_weekly(s: Site, reports: list[dict], period: str = "week") -> list[dict]:
    """The weekly (or monthly) reports, newest first. Held to the News rule: a
    report that names a declaration Lean has not verified stops the build."""
    P = PERIODS[period]
    out, seen = [], set()
    for r in reports:
        where = f"{P['news']} report {r.get('week', '?')!r}"
        if not P["label"].match(r.get("week", "")):
            raise ValueError(f"{where}: its label must be {P['format']}")
        if r.get("period", "week") != period:
            raise ValueError(f"{where}: it is a {r.get('period')} report, not a {P['news']} one")
        if r.get("format") != WEEKLY_FORMAT:
            raise ValueError(f"{where}: format {r.get('format')!r}, this build reads "
                             f"{WEEKLY_FORMAT}; regenerate it with `aftd interpret --{period}`")
        if r["week"] in seen:
            raise ValueError(f"{where}: two reports for one {P['noun']}")
        seen.add(r["week"])
        for k in ("start", "end"):
            time.strptime(r.get(k, ""), "%Y-%m-%d")
        results = [x for f in r.get("fields") or [] for x in f.get("results") or []]
        if not (r.get("title") or "").strip() or not results:
            raise ValueError(f"{where}: needs a title and results")
        for x in results:
            if x.get("outcome") not in WEEKLY_OUTCOMES:
                raise ValueError(f"{where}: unknown outcome {x.get('outcome')!r}")
            names = x.get("declarations") or []
            bad = [n for n in names if n not in s.by_name or not s.verified(s.by_name[n])]
            if bad:
                raise ValueError(f"{where}: not a verified theorem: {', '.join(bad)}")
            if x.get("main") not in names:
                raise ValueError(f"{where}: {x.get('main')!r} is not among its declarations")
        out.append(r)
    return sorted(out, key=lambda r: r["week"], reverse=True)


def slug(name: str) -> str:
    """A declaration name as a URL segment. Lean names here are plain
    identifiers; anything else is percent-encoded rather than guessed at."""
    return name if _SAFE_NAME.match(name) else quote(name, safe="")


def day(ts: float | str) -> str:
    if isinstance(ts, str):
        return ts[:10]
    return time.strftime("%d %b %Y", time.gmtime(ts)) if ts else ""


def clip(text: str, n: int) -> str:
    text = " ".join((text or "").split())
    return text if len(text) <= n else text[: n - 1].rsplit(" ", 1)[0] + "…"


def money(x: float, currency: str) -> str:
    sym = {"USD": "$", "EUR": "€", "GBP": "£", "CNY": "¥"}.get(currency)
    return f"{sym}{x:,.2f}" if sym else f"{x:,.2f} {currency}"


# ------------------------------------------------------------ lean syntax
# Enough highlighting to make a proof scannable, not a Lean parser: comments,
# declaration and term keywords, common tactics, sorts. Anything unrecognised
# is left plain, which is always a safe failure.
_LEAN_DECL = (
    "theorem lemma def abbrev structure class instance inductive where namespace "
    "section end open variable universe noncomputable private protected example"
).split()
_LEAN_TERM = "fun let have show by if then else match with from at in calc do return".split()
_LEAN_TACTIC = (
    "intro intros obtain exact exacts apply refine rw rwa simp simpa dsimp simp_all "
    "omega linarith nlinarith norm_num ring ring_nf field_simp positivity gcongr "
    "constructor use cases rcases induction by_contra by_cases unfold aesop tauto "
    "decide trivial contradiction exfalso left right ext funext congr specialize "
    "push_neg subst rfl split_ifs split infer_instance assumption filter_upwards "
    "calc conv norm_cast push_cast exact_mod_cast change set generalize"
).split()
_LEAN_TOKEN = re.compile(
    r"(?P<c>/-.*?-/|--[^\n]*)"
    r"|(?P<w>[A-Za-z_][A-Za-z0-9_'!?.]*)"
    r"|(?P<o>[^A-Za-z_/-]+|.)",
    re.S,
)


def highlight_lean(src: str) -> str:
    """Lean source as escaped HTML with <span> classes for the stylesheet."""
    out = []
    for m in _LEAN_TOKEN.finditer(src):
        text = m.group(0)
        if m.group("c"):
            out.append(f'<span class="lc">{e(text)}</span>')
        elif m.group("w"):
            cls = (
                "lk" if text in _LEAN_DECL
                else "lt" if text in _LEAN_TERM
                else "lx" if text in _LEAN_TACTIC
                else "ls" if text in ("Type", "Prop", "Sort", "Type*")
                else ""
            )
            out.append(f'<span class="{cls}">{e(text)}</span>' if cls else e(text))
        else:
            out.append(e(text))
    return "".join(out)


# ------------------------------------------------------------------- layout
NAME = "AFTD"
FULL_NAME = "Auto-Formalizing Theoretical Domains"
NAV = [
    ("knowledgebase/", "Knowledgebase"),
    ("reports/", "Summary Reports"),
    ("problems/", "Open Problems"),
]


def page(
    s: Site,
    *,
    title: str,
    root: str,
    active: str,
    body: str,
    description: str = "",
    math: bool = False,
    script: bool = False,
    wide: bool = False,
) -> str:
    current = ' aria-current="page"'
    links = "".join(
        f'<a href="{root}{href}"{current if href == active else ""}>{label}</a>'
        for href, label in NAV
    )
    head_math = (
        f'<link rel="stylesheet" href="{KATEX}/katex.min.css">'
        f'<script defer src="{KATEX}/katex.min.js"></script>'
        f'<script defer src="{KATEX}/contrib/auto-render.min.js"></script>'
        if math
        else ""
    )
    tail = (
        f'<script src="{root}static/app.js"></script>' if (script or math or wide) else ""
    )
    full = f"{title} · {NAME}" if title != NAME else f"{NAME} · {FULL_NAME}"
    t = s.kb["totals"]
    main = f'<main class="home">{body}</main>' if wide else f'<main class="wrap">{body}</main>'
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{e(full)}</title>
<meta name="description" content="{e(description or s.cfg.get('description', ''))}">
<meta property="og:title" content="{e(full)}">
<meta property="og:description" content="{e(description or s.cfg.get('description', ''))}">
<link rel="icon" href="{root}static/icon.svg" type="image/svg+xml">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="{FONTS}">
<link rel="stylesheet" href="{root}static/style.css">
{head_math}
</head>
<body>
<header class="site">
  <div class="bar-in">
    <a class="brand" href="{root}index.html" aria-label="{NAME}, {FULL_NAME}: home">
      <img src="{root}static/icon.svg" alt="" width="26" height="26">
      <span class="brand-name">{NAME}</span>
      <span class="brand-full">{FULL_NAME}</span>
    </a>
    <nav aria-label="Site">{links}
      <a class="ext" href="{e(s.discussions())}">Discuss</a>
      <a class="ext" href="{e(s.gh)}">GitHub</a>
    </nav>
  </div>
</header>
{main}
<footer class="site">
  <div class="wrap foot-grid">
    <div class="foot-id">
      <p class="foot-name"><img src="{root}static/icon.svg" alt="" width="22" height="22">
      <strong>{NAME}</strong> &middot; {FULL_NAME}</p>
      <p class="foot-motto">Open proof to the community. Open verdict by the community.</p>
      <p>A declaration is listed only when Lean&nbsp;4 elaborated it against Mathlib
      and <code>#print axioms</code> returned nothing outside
      <code>{e(" · ".join(s.kb["trusted_axioms"]))}</code>. Every one of them
      rebuilds offline from <a href="{e(s.blob("lean/AFTD"))}">the Lean sources</a>
      with <code>lake build</code>.</p>
    </div>
    <div class="foot-col">
      <h2>Explore</h2>
      <a href="{root}knowledgebase/">Knowledgebase</a>
      <a href="{root}knowledgebase/#graph">Dependency graph</a>
      <a href="{root}problems/">Open Problems</a>
      <a href="{root}index.html#news">News</a>
      <a href="{root}reports/">Summary Reports</a>
      <a href="{root}chat/">Chat with Knowledgebase</a>
      <a href="{root}problems/#submit">Submit a problem</a>
    </div>
    <div class="foot-col">
      <h2>Take part</h2>
      <a href="{e(s.discussions())}">Discussions</a>
      <a href="{e(s.new_verdict())}">Challenge a result</a>
      <a href="{e(s.blob("assets/README_AFTD.MD"))}">The programme</a>
      <a href="{e(s.gh)}">Source on GitHub</a>
    </div>
  </div>
  <div class="wrap foot-base">Snapshot of {t["declarations"]} declarations, taken
  {e(s.kb["generated"][:10])}. Take the Lean, use it, build on it &mdash; you do not
  owe us a citation.</div>
</footer>
{tail}
</body>
</html>
"""


# -------------------------------------------------------------- fragments
def badge(text: str, cls: str = "", title: str = "") -> str:
    t = f' title="{e(title)}"' if title else ""
    return f'<span class="badge {cls}"{t}>{e(text)}</span>'


def status_badge(st: str) -> str:
    return badge(STATUSES.get(st, st), f"st-{st}")


def decl_link(root: str, name: str) -> str:
    return f'<a class="decl" href="{root}d/{slug(name)}/">{e(name)}</a>'


def searchable(*texts: str) -> str:
    """Text as the knowledgebase search sees it: lower case, with Lean's `_` and `.`
    as spaces, so "condorcet unique" finds `condorcet_winner_unique`. app.js
    normalises the query the same way."""
    return " ".join(re.sub(r"[_.\s]+", " ", " ".join(texts).lower()).split())


def inline_code(text: str) -> str:
    """Escaped text with `backticked` spans set as code, the way the models
    write Lean names into their prose."""
    return re.sub(r"`([^`\n]+)`", r"<code>\1</code>", e(text))


def kind_badge(d: dict) -> str:
    return badge(d["kind"], "kind def" if d["is_def"] else "kind thm")


# Where a result comes from (aftd/kb/provenance.py), as the reader sees it:
# label, badge class, what the badge means, and what the citation is to it.
PROVENANCE = {
    "literature": ("formalization", "prov-lit",
                   "A published result, restated and proved in Lean. The result is the "
                   "cited source's; Lean checks this statement of it.", "Formalizes"),
    "original": ("original", "orig",
                 "Not taken from a source: stated and proved here. The related work we "
                 "found is cited; it may still turn out to be known.", "Related work"),
    "erratum": ("erratum", "prov-err",
                "Lean shows the cited published claim to be false or incomplete", "Corrects"),
}


def provenance_badge(d: dict) -> list[str]:
    """The provenance badge of a declaration, if it has one. A transcribed
    definition gets none: there is no result to credit, only its citation."""
    p = PROVENANCE.get(d.get("provenance") or "")
    if not p or (p[0] == "formalization" and d.get("is_def")):
        return []
    return [badge(p[0], p[1], p[2])]


def decl_card(s: Site, d: dict, root: str, *, sig: bool = True) -> str:
    """One declaration in a list: what it says in words first, the Lean name
    and signature second, and the whole card is the link to the rest."""
    tags = [kind_badge(d), *provenance_badge(d)]
    if d.get("problem") is not None:
        tags.append(badge(f"problem #{d['problem']}", "comm"))
    if d.get("explanation"):
        tags.append(badge("explained", "expl", "the proof is explained in words"))
    if s.challenges.get(d["name"]):
        tags.append(badge("challenged", "chal", "someone has questioned this result"))
    meta = [f'<span class="m-topic">{e(s.topic_title(d["topic"]))}</span>']
    if d.get("citation"):
        meta.append(f'<span class="m-src" title="{e(d["citation"])}">{e(clip(d["citation"], 80))}</span>')
    elif d.get("provenance") == "lemma":
        meta.append('<span title="Filed by the prover as a step towards another result">helper lemma</span>')
    if d["used_by"]:
        meta.append(f'<span>used by {len(d["used_by"])}</span>')
    meta.append(f'<span>{e(day(d["proved_at"]))}</span>')
    hay = searchable(
        d["name"], d["informal"], s.topic_title(d["topic"]), s.domain_title(d["domain"]),
        d.get("citation") or "", d["statement"],
    )
    words = d["informal"] or d["statement"]
    return (
        f'<article class="card entry" data-q="{e(hay)}" data-domain="{e(d["domain"])}" '
        f'data-kind="{"def" if d["is_def"] else "theorem"}" '
        f'data-community="{"1" if d.get("problem") is not None else "0"}" '
        f'data-t="{d["proved_at"]}" data-seq="{d["seq"]}">'
        f'<div class="card-top"><a class="decl stretch" href="{root}d/{slug(d["name"])}/">{e(d["name"])}</a>'
        f'<span class="badges">{"".join(tags)}</span></div>'
        f'<p class="prose">{e(words)}</p>'
        + (f'<pre class="sig lean">{highlight_lean(d["statement"])}</pre>' if sig else "")
        + f'<p class="meta">{"".join(meta)}</p></article>'
    )


def open_card(s: Site, n: dict, root: str) -> str:
    """A statement in the knowledgebase that Lean has not proved (yet).

    It is listed where it belongs, so a reader sees what the machine is working
    on, but marked as unproved and with no result page: nothing about it is
    verified beyond the statement type-checking."""
    st = "stuck" if n.get("status") == "stuck" else "open"
    tags = [badge(n["kind"], "kind thm"),
            badge("needs help" if st == "stuck" else "not yet proved", "st-unproved",
                  "Stated and type-checked in Lean, not proved"), *provenance_badge(n)]
    meta = [f'<span class="m-topic">{e(s.topic_title(n["topic"]))}</span>']
    if n.get("citation"):
        meta.append(f'<span class="m-src" title="{e(n["citation"])}">{e(clip(n["citation"], 80))}</span>')
    if n.get("created"):
        meta.append(f'<span>posed {e(day(n["created"]))}</span>')
    hay = searchable(n["name"], n["informal"], s.topic_title(n["topic"]),
                     s.domain_title(n["domain"]), n.get("citation") or "", n["statement"])
    return (
        f'<article class="card entry unproved" data-q="{e(hay)}" data-domain="{e(n["domain"])}" '
        f'data-kind="open" data-community="{"1" if n.get("problem") is not None else "0"}" '
        f'data-t="{n.get("created") or 0}" data-seq="0">'
        f'<div class="card-top"><code class="decl">{e(n["name"])}</code>'
        f'<span class="badges">{"".join(tags)}</span></div>'
        f'<p class="prose">{e(n["informal"] or n["statement"])}</p>'
        f'<pre class="sig lean">{highlight_lean(n["statement"])}</pre>'
        f'<p class="meta">{"".join(meta)}</p></article>'
    )


def problem_card(s: Site, p: dict, root: str) -> str:
    f = p["fields"]
    meta = [status_badge(p["status"])]
    if f.get("domain"):
        meta.append(badge(f["domain"], "dom"))
    answered = s.answers.get(p["number"], [])
    ans = ""
    if answered:
        ans = (
            '<p class="answers">Answered by '
            + ", ".join(decl_link(root, n["name"]) if n["name"] in s.by_name
                        else f'<code>{e(n["name"])}</code>' for n in answered)
            + "</p>"
        )
    who = f' · posed by <a href="https://github.com/{e(p["author"])}">@{e(p["author"])}</a>' if p["author"] else ""
    return (
        f'<article class="card problem">'
        f'<div class="card-top"><a class="ptitle" href="{root}problems/{p["number"]}/">'
        f'<span class="num">#{p["number"]}</span> {e(p["title"])}</a>'
        f'<span class="badges">{"".join(meta)}</span></div>'
        f'<p class="prose math">{e(clip(f.get("statement", ""), 420))}</p>'
        f'{ans}<p class="small">opened {e(day(p["created_at"]))}{who}</p></article>'
    )


def news_href(root: str, href: str) -> str:
    """A link from news.json: absolute URLs and anchors as written, anything
    else relative to the site root."""
    return href if re.match(r"^([a-z][a-z0-9+.-]*:|#)", href) else root + href


def news_paras(text: str) -> list[str]:
    return [inline_code(" ".join(p.split())) for p in re.split(r"\n\s*\n", text.strip())]


def news_date(n: dict) -> str:
    return (
        f'<time datetime="{e(n["date"])}">'
        f'{e(time.strftime("%d %b %Y", time.strptime(n["date"], "%Y-%m-%d")))}</time>'
    )


NEWS_SHOWN = 4  # entries open on the home page; older ones sit behind a toggle


def news_item(s: Site, n: dict, root: str) -> str:
    """One announcement in the home page's News section: its title and first
    paragraph, and the rest -- further paragraphs, the declarations a proof
    announcement names, its links -- one click away."""
    kind = badge(NEWS_KINDS[n["kind"]], "nk-" + n["kind"])
    paras = news_paras(n["body"])
    more = "".join(f'<p class="prose">{p}</p>' for p in paras[1:])
    if n["declarations"]:
        label = "Verified in Lean" if n["kind"] in ("proof", "daily") else "Declarations"
        more += (
            f'<div class="news-decls"><span class="small">{label}</span>'
            + related(s, n["declarations"], root)
            + "</div>"
        )
    links = "".join(
        f'<a href="{e(news_href(root, l["href"]))}">{e(l["label"])} &rarr;</a>'
        for l in n["links"]
    )
    if more:
        what = (
            f'{len(n["declarations"])} declaration{"s" if len(n["declarations"]) != 1 else ""} verified in Lean'
            if n["kind"] == "proof"
            else "Details"
        )
        more = f'<details class="news-more"><summary>{what}</summary>{more}</details>'
    return (
        f'<article class="news-item" id="{e(n["id"])}">'
        f'<p class="news-when">{news_date(n)}{kind}</p>'
        f'<div class="news-main"><h3><a href="#{e(n["id"])}">{e(n["title"])}</a></h3>'
        f'<p class="prose">{paras[0]}</p>{more}'
        + (f'<p class="news-links">{links}</p>' if links else "")
        + "</div></article>"
    )


def news_section(s: Site, root: str) -> str:
    if not s.news:
        return ""
    items = "".join(news_item(s, n, root) for n in s.news[:NEWS_SHOWN])
    older = s.news[NEWS_SHOWN:]
    if older:
        items += (
            f'<details class="news-older"><summary>Earlier news ({len(older)})</summary>'
            + "".join(news_item(s, n, root) for n in older)
            + "</details>"
        )
    return (
        '<section class="wrap band news-band" id="news">'
        '<header class="band-head"><p class="eyebrow">News</p>'
        "<h2>Launches and newly proved results</h2></header>"
        f'<div class="news-list">{items}</div></section>'
    )


# ------------------------------------------------------------------- pages
def featured(s: Site) -> list[dict]:
    """Declarations to show in the hero: configured in site.json, else a few
    short theorems -- long enough to look like a proof, short enough to read."""
    names = [n for n in s.cfg.get("featured") or [] if n in s.by_name]
    if names:
        return [s.by_name[n] for n in names]
    pool = [d for d in s.decls if not d["is_def"] and 250 <= len(d["source"]) <= 700]
    return sorted(pool, key=lambda d: d["seq"])[:3]


def proof_window(s: Site, items: list[dict], root: str) -> str:
    """The hero's code window: a verified theorem, in words and in Lean."""
    if not items:
        return ""
    tabs, panels = [], []
    for i, d in enumerate(items):
        on = i == 0
        tabs.append(
            f'<button class="pw-tab{" on" if on else ""}" role="tab" '
            f'aria-selected="{"true" if on else "false"}" data-pw="{i}">'
            f'{e(s.topic_title(d["topic"]))}'
            "</button>"
        )
        file = (d.get("lean_path") or "").rsplit("/", 1)[-1] or f'{d["name"]}.lean'
        axioms = " · ".join(d["axioms"])
        panels.append(
            f'<div class="pw-panel{"" if on else " hidden"}" role="tabpanel" data-pw="{i}">'
            f'<div class="pw-bar"><span class="dots"><i></i><i></i><i></i></span>'
            f'<span class="pw-file">{e(file)}</span></div>'
            f'<p class="pw-says">{e(clip(d["informal"], 190))}</p>'
            f'<pre class="lean pw-code">{highlight_lean(d["source"])}</pre>'
            f'<div class="pw-status"><span class="pw-ok">'
            f'<svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true">'
            f'<path d="M3 8.5l3 3 7-7" fill="none" stroke="currentColor" stroke-width="2.2" '
            f'stroke-linecap="round" stroke-linejoin="round"/></svg> Lean accepted</span>'
            f'<span class="pw-ax">axioms: {e(axioms)}</span>'
            f'<a href="{root}d/{slug(d["name"])}/">Open &rarr;</a></div></div>'
        )
    tablist = (
        f'<div class="pw-tabs" role="tablist" aria-label="Featured results">{"".join(tabs)}</div>'
        if len(items) > 1
        else ""
    )
    return f'<div class="pw">{tablist}{"".join(panels)}</div>'


def stat(value: str, label: str, sub: str = "") -> str:
    return (
        f'<div class="stat"><span class="stat-v">{value}</span>'
        f'<span class="stat-k">{e(label)}</span>'
        + (f'<span class="stat-s">{e(sub)}</span>' if sub else "")
        + "</div>"
    )


def render_home(s: Site) -> str:
    root = ""
    t = s.kb["totals"]
    doms = s.kb["domains"]
    n_topics = sum(len(d["topics"]) for d in doms)
    target = sum(tp["target"] for d in doms for tp in d["topics"])
    opened = sum(1 for d in doms if any(tp["proved"] for tp in d["topics"]))
    prov = provenance_counts(s)
    per = t["spend"] / t["declarations"] if t["declarations"] else 0.0

    recent = sorted(s.decls, key=lambda d: (-d["proved_at"], -d["seq"]))[:5]
    shown = [p for p in s.problems if p["status"] not in ("pending", "declined")]
    shown.sort(key=lambda p: (list(STATUSES).index(p["status"]), -p["number"]))
    pending = sum(1 for p in s.problems if p["status"] == "pending")
    if shown:
        probs = "".join(problem_card(s, p, root) for p in shown[:3])
    else:
        probs = (
            '<div class="card empty-card"><p class="prose">No community problems '
            "yet. Pose the first one: a statement from any of the six domains, "
            "with a reference if you have one.</p>"
            f'<a class="btn primary" href="{e(s.new_problem())}">Submit a problem</a></div>'
        )
    if pending:
        probs += (
            f'<p class="small">{pending} more submission{"s" if pending != 1 else ""} '
            f'<a href="{e(s.pending_url())}">awaiting review</a>.</p>'
        )

    steps = [
        ("Propose", "The Proposer works one topic at a time: it transcribes known "
         "results from the literature and proposes its own &mdash; generalizations, "
         "converses, bridges between topics."),
        ("Round-trip", "One model reads only the Lean and says what it asserts; another "
         "reads only the English and formalizes it blind. Lean is asked first "
         "whether the two agree."),
        ("Prove", "The Prover takes one statement at a time. When it is stuck it files "
         "the lemmas it needs and the graph grows a rung &mdash; it never quietly "
         "proves something weaker."),
        ("Publish", "Lean elaborates it, <code>#print axioms</code> is clean, and it "
         "goes public with its full source, rebuildable by anyone with "
         "<code>lake build</code>."),
    ]
    flow = "".join(
        f'<li><span class="step-n">{i}</span><h3>{name}</h3><p>{text}</p></li>'
        for i, (name, text) in enumerate(steps, start=1)
    )

    dom_cards = []
    for d in doms:
        proved = sum(tp["proved"] for tp in d["topics"])
        tgt = sum(tp["target"] for tp in d["topics"]) or 1
        pct = min(100, 100 * proved / tgt)
        live = proved > 0
        tag = (
            '<span class="badge ok">open</span>'
            if live
            else '<span class="badge">waiting on compute</span>'
        )
        head = (
            f'<a href="knowledgebase/#d-{e(d["name"])}">{e(d["title"])}</a>'
            if live
            else e(d["title"])
        )
        dom_cards.append(
            f'<article class="dom{" live" if live else ""}">'
            f'<div class="dom-top">{tag}</div><h3>{head}</h3>'
            f'<p>{e(clip(d["description"], 150))}</p>'
            f'<div class="dom-meter"><span style="width:{max(pct, 0.8 if live else 0):.1f}%"></span></div>'
            f'<p class="dom-n"><strong>{proved}</strong> of {tgt:,} targeted &middot; '
            f'{len(d["topics"])} topics</p></article>'
        )

    body = f"""
<section class="hero-band">
  <div class="wrap hero-grid">
    <div class="hero-copy">
      <p class="eyebrow"><span class="acr">{NAME}</span> An open research programme</p>
      <h1>{FULL_NAME}</h1>
      <p class="motto">Open proof to the community.<br>Open verdict by the community.</p>
      <p class="lead">A machine that reads a curriculum of the theoretical sciences,
      states their theorems in Lean&nbsp;4, proves them against Mathlib, and
      publishes whatever Lean accepts &mdash; immediately, to everyone, with no
      paper and no author line. Nothing is here because a language model said it
      was true.</p>
      <div class="cta">
        <a class="btn primary" href="problems/#submit">Submit a problem</a>
        <a class="btn" href="knowledgebase/">Browse the knowledgebase</a>
      </div>
    </div>
    <div class="hero-card">{proof_window(s, featured(s), root)}</div>
  </div>
</section>

{news_section(s, root)}
<section class="stats-band">
  <div class="wrap stats">
    {stat(f'{t["declarations"]:,}', "machine-verified declarations",
          f'{t["theorems"]} theorems · {t["definitions"]} definitions')}
    {stat(str(t["topics"]), "topics with results", f"across {opened} of {len(doms)} domains")}
    {stat(f"{target:,}", "declarations in the curriculum", f"{n_topics} topics, {len(doms)} domains")}
    {stat(money(t["spend"], t["currency"]).split(".")[0], "API spend to date",
          f"about {round(per * 100)}¢ per verified declaration" if per else "")}
  </div>
</section>

<section class="wrap band manifesto">
  <blockquote>Point a loop at a curriculum of theoretical domains. Let it state and
  prove, forever. Keep only what Lean accepts. Publish all of it, immediately, to
  everyone.</blockquote>
  <div class="manifesto-text">
    <p>Theory is written to be read by people, and it is checked by people. That
    checking is the bottleneck: it does not scale, it is unevenly spread across
    subjects, and most of it is never written down in a form another person or
    machine can reuse.</p>
    <p>Lean&nbsp;4 and Mathlib remove the bottleneck for the <em>checking</em>.
    {NAME} automates the other half &mdash; deciding what is worth stating,
    writing the statement, attempting the proof &mdash; a subject at a time, not
    a paper at a time. The unit of progress is one Lean declaration that anyone
    can <code>import</code> tomorrow.</p>
    <a href="{e(s.blob("assets/README_AFTD.MD"))}">Read the programme &rarr;</a>
  </div>
</section>

<section class="wrap band">
  <header class="band-head"><p class="eyebrow">How it works</p>
  <h2>Three agents, one dependency graph, and Lean as the only judge</h2></header>
  <ol class="flow">{flow}</ol>
  <p class="band-note">The scheduler is not a language model. What to work on, when
  to give up and when to split a hard theorem into lemmas are deterministic rules
  over the graph; the models supply judgement, never control flow.</p>
</section>

<section class="wrap band">
  <header class="band-head"><p class="eyebrow">The curriculum</p>
  <h2>Six theoretical domains</h2>
  <p class="lead">{opened} are open so far; the rest are waiting on compute, not on
  code.</p></header>
  <div class="doms">{"".join(dom_cards)}</div>
</section>

<section class="wrap band">
  <header class="band-head"><p class="eyebrow">Take part</p>
  <h2>Pose, read, judge</h2></header>
  <div class="three">
    <div class="panel"><span class="panel-n">01</span><h3>Pose a problem</h3>
    <p>Send a statement through a GitHub issue. Once reviewed, the machine
    formalizes it, checks the formalization says what you said, and tries to
    prove it. Your handle stays on it.</p>
    <a href="problems/#submit">How submitting works &rarr;</a></div>
    <div class="panel"><span class="panel-n">02</span><h3>Read the proofs</h3>
    <p>Every verified declaration has its own page: the statement in words and in
    Lean, the full proof, what it builds on and what builds on it.</p>
    <a href="knowledgebase/">The knowledgebase &rarr;</a></div>
    <div class="panel"><span class="panel-n">03</span><h3>Judge the verdicts</h3>
    <p>Correctness is settled by Lean. Everything else is yours to dispute: a name
    that claims too much, a trivial statement, a definition the subject would not
    recognise.</p>
    <a href="{e(s.new_verdict())}">Challenge a result &rarr;</a></div>
  </div>
</section>

<section class="wrap band split">
  <div>
    <header class="shead"><h2>Community problems</h2><a href="problems/">All open problems &rarr;</a></header>
    {probs}
  </div>
  <div>
    <header class="shead"><h2>Recently verified</h2><a href="knowledgebase/">Knowledgebase &rarr;</a></header>
    {"".join(decl_card(s, d, root, sig=False) for d in recent)}
  </div>
</section>

<section class="wrap band rules-grid">
  <div class="rules">
    <h2>What &ldquo;proved&rdquo; means here</h2>
    <ul class="checks">
      <li><strong>Lean elaborates it</strong> against Mathlib, with zero errors.</li>
      <li><strong><code>#print axioms</code> is clean</strong>: nothing beyond
      <code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>
      &mdash; which rules out <code>sorry</code>, <code>native_decide</code> and any
      axiom an agent declared for itself.</li>
      <li><strong>It survives the round trip</strong>: the Lean and the English are
      each read blind and must agree.</li>
      <li><strong>Its name claims no more than it proves</strong>, and it does not
      privately re-invent a concept Mathlib already has.</li>
    </ul>
  </div>
  <div class="rules not">
    <h2>What this is not</h2>
    <p>It is not a claim that mathematicians are replaceable, and it takes no
    credit for other people's results. Most of the knowledgebase is known mathematics:
    {prov["literature"]} theorems formalize a published result, and each one says so
    and credits its source. {prov["original"]} were stated here, most of them answers
    to questions that papers leave open; they cite the related work we found and
    may still turn out to be known.{f' {prov["erratum"]} show a published claim to be false or incomplete.' if prov["erratum"] else ""}
    The value is in the aggregate &mdash; verified, open and cumulative &mdash; not
    in any single line of it.</p>
    <p>No one on this side takes an author line, and there will be no paper.</p>
  </div>
</section>

<section class="support-band">
  <div class="wrap support">
    <div>
      <h2>The only real cost is tokens.</h2>
      <p>Fund the run with API credits and you are acknowledged on the results
      &mdash; specifically: what you gave, what was spent, and which verified
      results your money paid for. Money buys attempts, not results; a name on the
      board is support, not authorship.</p>
    </div>
    <div class="cta">
      <a class="btn primary" href="{e(s.gh)}/issues/new?title=Funding">Support the research</a>
      <a class="btn ghost" href="{e(s.discussions())}">Join the discussion</a>
    </div>
  </div>
</section>
"""
    return page(s, title=NAME, root=root, active="", body=body, math=bool(shown), wide=True)


def provenance_counts(s: Site) -> dict[str, int]:
    """How many theorems carry each provenance badge."""
    return {k: sum(1 for d in s.decls if not d["is_def"] and d.get("provenance") == k)
            for k in PROVENANCE}


def provenance_key(s: Site) -> str:
    """What the provenance badges mean, with how many theorems carry each."""
    n = provenance_counts(s)
    return (
        f'<p class="small prov-key">{provenance_badge({"provenance": "literature"})[0]} '
        f'{n["literature"]} theorems formalize a published result: the result is the '
        f'cited source\'s, and Lean checks our statement of it. '
        f'{provenance_badge({"provenance": "original"})[0]} {n["original"]} were stated '
        f'here, not taken from a source, with the related work cited where we found any. '
        + (f'{provenance_badge({"provenance": "erratum"})[0]} {n["erratum"]} show a '
           f'published claim false or incomplete. ' if n["erratum"] else "")
        + "The other theorems are helper lemmas towards these.</p>"
    )


def render_kb(s: Site) -> str:
    root = "../"
    by_dom: dict[str, dict[str, list[dict]]] = {}
    for d in s.decls:
        by_dom.setdefault(d["domain"], {}).setdefault(d["topic"], []).append(d)
    # Unproved theorems sit with their topic, after what is proved there.
    unproved = [n for n in s.open if n.get("kind") == "theorem"]
    for n in unproved:
        by_dom.setdefault(n["domain"], {}).setdefault(n["topic"], []).append({**n, "_open": True})
    order = [n for n in s.domains if n in by_dom] + sorted(
        n for n in by_dom if n not in s.domains
    )
    sections, toc, options = [], [], []
    for dom in order:
        topics = by_dom[dom]
        count = sum(len(v) for v in topics.values())
        options.append(f'<option value="{e(dom)}">{e(s.domain_title(dom))} ({count})</option>')
        blocks, toc_topics = [], []
        for tname in sorted(topics, key=lambda t: -len(topics[t])):
            ds = topics[tname]
            n_proved = sum(1 for d in ds if not d.get("_open"))
            target = (s.topics.get(tname) or {}).get("target") or 0
            bar = ""
            if target:
                pct = min(100, round(100 * n_proved / target))
                bar = (
                    f'<span class="meter" title="{n_proved} of a target of {target}">'
                    f'<span style="width:{pct}%"></span></span>'
                    f'<span class="tnum">{n_proved} of {target} targeted</span>'
                )
            blocks.append(
                f'<section class="topic" id="t-{e(tname)}"><header class="thead">'
                f"<h3>{e(s.topic_title(tname))}</h3>{bar}</header>"
                + "".join(open_card(s, d, root) if d.get("_open") else decl_card(s, d, root)
                          for d in ds)
                + "</section>"
            )
            toc_topics.append(
                f'<li><a href="#t-{e(tname)}" data-sec="t-{e(tname)}">'
                f'<span>{e(s.topic_title(tname))}</span><span class="c">{len(ds)}</span></a></li>'
            )
        desc = (s.domains.get(dom) or {}).get("description") or ""
        sections.append(
            f'<section class="domain" id="d-{e(dom)}"><header class="dhead">'
            f'<h2>{e(s.domain_title(dom))}</h2><span class="n">{count}</span></header>'
            + (f'<p class="lede">{e(desc)}</p>' if desc else "")
            + "".join(blocks)
            + "</section>"
        )
        toc.append(
            f'<li class="toc-d"><a href="#d-{e(dom)}" data-sec="d-{e(dom)}">'
            f'<span>{e(s.domain_title(dom))}</span><span class="c">{count}</span></a>'
            f'<ul>{"".join(toc_topics)}</ul></li>'
        )
    t = s.kb["totals"]
    community = (
        '<label class="switch"><input type="checkbox" id="f-community"> From community problems</label>'
        if any(d.get("problem") is not None for d in s.decls)
        else ""
    )
    body = f"""
<header class="phead">
  <p class="eyebrow">Verified in Lean&nbsp;4</p>
  <h1>Knowledgebase</h1>
  <p class="lead full">{t["declarations"]} declarations &mdash; {t["theorems"]} theorems and
  {t["definitions"]} definitions in {t["topics"]} topics &mdash; each elaborated by
  Lean&nbsp;4 against Mathlib, with nothing outside the trusted axioms. The graph
  shows what each one builds on; the list below has them all, by topic.
  {f"It also lists, marked <em>not yet proved</em>, the {len(unproved)} statements the machine has posed and not proved: they type-check in Lean, and nothing more is claimed for them." if unproved else ""}</p>
  {provenance_key(s)}
</header>
{graph_section(s, root)}
<h2 class="rhead" id="list">Every declaration</h2>
<div class="rlayout">
  <aside class="toc">
    <details id="toc" open>
      <summary>Topics</summary>
      <nav aria-label="Topics"><ul>{"".join(toc)}</ul></nav>
    </details>
  </aside>
  <div class="rmain">
    <div class="toolbar">
      <div class="search">
        <label class="vh" for="q">Search declarations</label>
        <input id="q" type="search" placeholder="Search in words or by Lean name" autocomplete="off">
        <kbd aria-hidden="true">/</kbd>
      </div>
      <div class="controls">
        <div class="seg" role="group" aria-label="Kind">
          <button type="button" data-kind="all" aria-pressed="true">All</button>
          <button type="button" data-kind="theorem" aria-pressed="false">Theorems</button>
          <button type="button" data-kind="def" aria-pressed="false">Definitions</button>
          {'<button type="button" data-kind="open" aria-pressed="false">Not yet proved</button>' if unproved else ""}
        </div>
        <label class="vh" for="f-domain">Domain</label>
        <select id="f-domain"><option value="all">Every domain</option>{"".join(options)}</select>
        <label class="vh" for="f-sort">Order</label>
        <select id="f-sort">
          <option value="topic">By topic</option>
          <option value="new">Newest first</option>
        </select>
        <label class="switch"><input type="checkbox" id="f-lean"> Show Lean</label>
        {community}
      </div>
    </div>
    <p class="rcount"><span id="count" aria-live="polite">{t["declarations"]} declarations</span>
    <button type="button" class="linkish" id="clear" hidden>Clear filters</button></p>
    <div id="kb" class="rlist grouped">
      <div id="grouped">{"".join(sections)}</div>
      <div id="flat" class="flat" hidden></div>
      <div id="empty" class="empty-card card" hidden>
        <p class="prose">Nothing matches. Try fewer words, or a name from the
        topic list.</p>
        <button type="button" class="btn" data-clear>Clear filters</button>
      </div>
    </div>
  </div>
</div>
{render_ack(s)}
"""
    return page(
        s,
        title="Knowledgebase",
        root=root,
        active="knowledgebase/",
        body=body,
        script=True,
        description=f'{len(s.decls)} machine-verified Lean 4 declarations.',
    )


def render_ack(s: Site) -> str:
    grants = list(s.grants.values())
    if not grants:
        return ""
    cur = s.kb["totals"]["currency"]
    rows = "".join(
        f'<li><span class="name">{e(g["funder"])}</span> '
        f'<span class="small">{money(g["amount"], cur)} given, '
        f'{money(g["spent"], cur)} spent, {g["results"]} result'
        f'{"s" if g["results"] != 1 else ""} carry this name</span></li>'
        for g in grants
    )
    return (
        '<section class="ack"><h2>Acknowledgements</h2><p class="prose">Every '
        "declaration cost tokens to find, to state, to fail at and to prove. These "
        f'people paid for them.</p><ul class="grants">{rows}</ul></section>'
    )


# Domain colours on the graph, in the order the snapshot lists the domains, so
# a domain keeps its colour when another one is added after it. style.css
# defines --g1 .. --g8 for light and dark; a ninth domain shares slot 8.
GRAPH_SLOTS = 8


def graph_data(s: Site) -> dict:
    """The graph as graph.js reads it: nodes as short arrays, and edges as
    index pairs (user, used), counting only edges between published nodes."""
    present = {d["domain"] for d in s.decls}
    doms = [n for n in s.domains if n in present] + sorted(present - set(s.domains))
    slot = {n: min(i, GRAPH_SLOTS - 1) for i, n in enumerate(n for n in s.domains)}
    for n in doms:
        slot.setdefault(n, GRAPH_SLOTS - 1)
    di = {n: i for i, n in enumerate(doms)}
    idx = {d["name"]: i for i, d in enumerate(s.decls)}
    nodes = [
        [
            d["name"],
            1 if d["is_def"] else 0,
            di[d["domain"]],
            s.topic_title(d["topic"]),
            clip(d["informal"], 240),
            slug(d["name"]),
        ]
        for d in s.decls
    ]
    edges = sorted(
        {(idx[d["name"]], idx[u]) for d in s.decls for u in d["deps"] if u in idx and u != d["name"]}
    )
    return {
        "domains": [[n, s.domain_title(n), slot[n] + 1] for n in doms],
        "nodes": nodes,
        "edges": [list(x) for x in edges],
    }


def graph_section(s: Site, root: str) -> str:
    """The top of the knowledgebase page: every declaration as a node, every
    use as an arrow. graph.js draws it; without JavaScript the list below
    still has everything."""
    data = graph_data(s)
    # Inside <script> only "</" can end the element early.
    blob = json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    n_thm = sum(1 for n in data["nodes"] if not n[1])
    legend = "".join(
        f'<button type="button" class="g-dom" data-dom="{i}" aria-pressed="true">'
        f'<span class="sw" style="background:var(--g{c})"></span>{e(title)}'
        f'<span class="c" data-dom-count="{i}"></span></button>'
        for i, (_, title, c) in enumerate(data["domains"])
    )
    return f"""
<section class="g-sec" id="graph" aria-labelledby="graph-h">
<div class="g-title"><div class="g-title-text"><h2 id="graph-h">Dependency graph</h2>
<p class="small">One node per declaration, with an arrow to each result its proof uses.
Click a node to follow its chain; double-click to open its proof.</p></div>
<a class="btn primary g-chat" href="{root}chat/"
  title="Ask questions about the knowledgebase in plain words, with your own API key">Chat with
  Knowledgebase <span class="g-chat-tag">Experimental</span></a></div>
<div class="g-bar">
  <div class="search g-search">
    <label class="vh" for="g-q">Find a declaration</label>
    <input id="g-q" type="search" placeholder="Find a theorem on the graph"
      autocomplete="off" role="combobox" aria-expanded="false" aria-controls="g-hits">
    <ul id="g-hits" class="g-hits" role="listbox" hidden></ul>
  </div>
  <div class="seg" role="group" aria-label="Nodes">
    <button type="button" data-defs="0" aria-pressed="true">Theorems</button>
    <button type="button" data-defs="1" aria-pressed="false">Theorems + definitions</button>
  </div>
  <div class="g-legend" role="group" aria-label="Domains, click to hide or show">{legend}</div>
</div>
<div class="g-layout">
  <div class="g-stage" id="g-stage">
    <canvas id="g-canvas" aria-label="Dependency graph of {len(data["nodes"])} declarations; the list below has the same declarations as text"></canvas>
    <div class="g-tip" id="g-tip" hidden></div>
    <div class="g-zoom">
      <button type="button" data-zoom="in" aria-label="Zoom in">+</button>
      <button type="button" data-zoom="out" aria-label="Zoom out">&minus;</button>
      <button type="button" data-zoom="fit" aria-label="Fit the graph to the view">Fit</button>
    </div>
    <p class="g-count small" id="g-count" aria-live="polite"></p>
    <noscript><p class="g-nojs">The graph needs JavaScript. The list below has
    every declaration, and each declaration page links what it uses and what
    uses it.</p></noscript>
  </div>
  <aside class="g-panel card" id="g-panel" aria-live="polite" hidden>
    <button type="button" class="g-close" id="g-close" aria-label="Close">&times;</button>
    <div id="g-sel"></div>
  </aside>
</div>
<div class="g-read" id="g-idle">
  <h3>How to read it</h3>
  <ul class="g-help">
    <li><span class="g-key thm"></span> theorem or lemma</li>
    <li><span class="g-key def"></span> definition</li>
    <li><span class="g-key arr"></span> uses &mdash; points at what the proof relies on</li>
    <li><span class="g-key big"></span> bigger &mdash; used by more results</li>
  </ul>
  <p class="small">{n_thm} theorems and {len(data["nodes"]) - n_thm} definitions,
  {len(data["edges"])} uses between them. Drag to pan, scroll or pinch to zoom,
  drag a node to move it, double-click a node to open its proof.</p>
</div>
<script type="application/json" id="g-data">{blob}</script>
<script src="{root}static/graph.js" defer></script>
</section>"""


def render_decl(s: Site, d: dict) -> str:
    root = "../../"
    badges = [kind_badge(d)]
    if s.verified(d):
        badges.append(badge("verified", "ok", "Lean accepted it, and #print axioms lists only trusted axioms"))
    badges += provenance_badge(d)
    parts = [
        f'<nav class="crumbs"><a href="{root}knowledgebase/">Knowledgebase</a> / '
        f'<a href="{root}knowledgebase/#d-{e(d["domain"])}">{e(s.domain_title(d["domain"]))}</a> / '
        f'<a href="{root}knowledgebase/#t-{e(d["topic"])}">{e(s.topic_title(d["topic"]))}</a></nav>',
        f'<header class="phead"><h1 class="mono">{e(d["name"])}</h1>'
        f'<div class="badges">{"".join(badges)}</div></header>',
    ]
    if d.get("problem") is not None:
        p = s.problem_by_number.get(d["problem"])
        title = f': {e(p["title"])}' if p else ""
        parts.append(
            f'<p class="note comm">This answers community problem '
            f'<a href="{root}problems/{d["problem"]}/">#{d["problem"]}{title}</a>.</p>'
        )
    if d["informal"]:
        parts.append(f'<p class="prose big">{e(d["informal"])}</p>')
    parts.append(
        f'<h2>Statement</h2>{codebox(highlight_lean(d["statement"]), "sig")}'
    )
    parts.append(decl_facts(s, d, root))
    if d.get("reading"):
        parts.append(
            '<div class="reading"><h3>Read back from the Lean</h3>'
            f'<p class="prose">{inline_code(d["reading"])}</p><p class="small">Written by a '
            "model that saw only the Lean, never the English above. If the two "
            "disagree, that is worth a challenge.</p></div>"
        )
    x = d.get("explanation")
    if x:
        steps = "".join(
            f'<li><p class="claim">{e(st["claim"])}'
            + (' <span class="auto">automation</span>' if st["automation"] else "")
            + f'</p><p class="why">{e(st["explanation"])}</p>'
            + (
                '<p class="uses">uses '
                + ", ".join(f"<code>{e(l)}</code>" for l in st["lemmas"])
                + "</p>"
                if st["lemmas"]
                else ""
            )
            + f'<pre class="lean">{highlight_lean(st["code"])}</pre></li>'
            for st in x["steps"]
        )
        gloss = (
            '<dl class="gloss">'
            + "".join(
                f"<dt><code>{e(k)}</code></dt><dd>{e(v)}</dd>"
                for k, v in x["glossary"].items()
            )
            + "</dl>"
            if x["glossary"]
            else ""
        )
        cav = (
            '<ul class="caveats">' + "".join(f"<li>{e(c)}</li>" for c in x["caveats"]) + "</ul>"
            if x["caveats"]
            else ""
        )
        parts.append(
            f'<h2>The proof, explained</h2><p class="prose">{e(x["summary"])}</p>'
            f'<ol class="steps">{steps}</ol>{gloss}{cav}'
            f'<p class="disclaim">{e(x["disclaimer"])}</p>'
        )
    src_link = (
        f' <a class="small" href="{e(s.blob(d["lean_path"]))}">view module on GitHub</a>'
        if d.get("lean_path")
        else ""
    )
    parts.append(
        f'<h2>Lean source{src_link}</h2>{codebox(highlight_lean(d["source"]), "src")}'
    )
    ch = s.challenges.get(d["name"], [])
    if ch:
        items = "".join(
            f'<li><a href="{e(v["url"])}">#{v["number"]} {e(v["title"])}</a> '
            f'{badge(v["state"], "st-" + v["state"])} '
            f'<span class="small">{e(v["fields"].get("reason", ""))}</span></li>'
            for v in ch
        )
        parts.append(f'<h2>Challenges</h2><ul class="list">{items}</ul>')
    parts.append(
        '<div class="actions">'
        f'<a class="btn" href="{root}knowledgebase/?n={quote(d["name"])}#graph">See it in the graph</a>'
        f'<a class="btn" href="{e(s.discussions(d["name"]))}">Discuss this result</a>'
        f'<a class="btn" href="{e(s.new_verdict(d["name"]))}">Challenge it</a></div>'
    )
    parts.append(pager(s, d, root))
    return page(
        s,
        title=d["name"],
        root=root,
        active="knowledgebase/",
        body="".join(parts),
        script=True,
        description=clip(d["informal"] or d["statement"], 180),
    )


def codebox(lean_html: str, cls: str) -> str:
    """A block of Lean with a copy button. The button stays hidden until
    app.js wires it up, so without JavaScript there is no dead control."""
    return (
        f'<div class="codebox"><button type="button" class="copy" hidden>Copy</button>'
        f'<pre class="{cls} lean">{lean_html}</pre></div>'
    )


def related(s: Site, names: list[str], root: str) -> str:
    """Declarations named by a dependency edge, each with what it says, so the
    reader can tell which one to follow without opening them all."""
    items = []
    for n in names:
        d = s.by_name.get(n)
        words = f'<span class="rel-w">{e(clip(d["informal"], 140))}</span>' if d and d["informal"] else ""
        items.append(f"<li>{decl_link(root, n)}{words}</li>")
    return f'<ul class="rel">{"".join(items)}</ul>'


def decl_facts(s: Site, d: dict, root: str) -> str:
    chips = "".join(
        f'<code class="{"ok" if a in s.kb["trusted_axioms"] else "bad"}">{e(a)}</code>'
        for a in d["axioms"]
    )
    if not chips:
        chips = (
            '<span class="small">none &mdash; Lean reports it depends on no axioms</span>'
            if not d["is_def"]
            else '<span class="small">none listed</span>'
        )
    rows = []
    prov = PROVENANCE.get(d.get("provenance") or "")
    if d.get("citation"):
        label = prov[3] if prov else "Source"
        if label == "Formalizes" and d["is_def"]:
            label = "Defined in"
        rows.append((label, e(d["citation"])))
    elif d.get("provenance") == "original":
        rows.append(("Source", "Stated here; not taken from a source"))
    elif d.get("provenance") == "lemma":
        rows.append(("Source", "Filed by the prover as a step towards another result"))
    rows.append(("Verified", e(day(d["proved_at"]))))
    rows.append(("Axioms", f'<span class="ax">{chips}</span>'))
    if d["deps"]:
        rows.append((f'Built on <span class="c">{len(d["deps"])}</span>', related(s, d["deps"], root)))
    if d["used_by"]:
        rows.append((f'Used by <span class="c">{len(d["used_by"])}</span>', related(s, d["used_by"], root)))
    g = s.grants.get(d.get("funder") or "")
    if g:
        rows.append(("Paid for by", e(g["funder"])))
    return '<dl class="kv">' + "".join(f"<dt>{k}</dt><dd>{v}</dd>" for k, v in rows) + "</dl>"


def pager(s: Site, d: dict, root: str) -> str:
    """Previous and next in the same topic, in knowledgebase-page order."""
    seq = s.in_topic.get(d["topic"], [])
    i = next((k for k, x in enumerate(seq) if x["name"] == d["name"]), -1)
    if i < 0 or len(seq) < 2:
        return ""

    def side(x: dict | None, cls: str, label: str) -> str:
        if not x:
            return f'<span class="{cls}"></span>'
        return (
            f'<a class="{cls}" href="{root}d/{slug(x["name"])}/"><span class="small">{label}</span>'
            f'<span class="mono">{e(x["name"])}</span></a>'
        )

    prev = seq[i - 1] if i > 0 else None
    nxt = seq[i + 1] if i + 1 < len(seq) else None
    return (
        f'<nav class="pager" aria-label="{e(s.topic_title(d["topic"]))}">'
        f'{side(prev, "prev", "&larr; Previous")}'
        f'<span class="pos small">{i + 1} of {len(seq)} in {e(s.topic_title(d["topic"]))}</span>'
        f'{side(nxt, "next", "Next &rarr;")}</nav>'
    )


def render_problems(s: Site) -> str:
    """Every open problem in one list, by status, wherever it comes from: the
    community's issues and the knowledgebase's open-problem list alike."""
    root = "../"

    def decl_href(name: str) -> str | None:
        return f"{root}d/{slug(name)}/" if name in s.by_name else None

    # status -> [(topic, card)], community problems newest first, then the list.
    groups: dict[str, list[tuple[str, str]]] = {k: [] for k in STATUSES}
    declined = []
    for p in sorted(s.problems, key=lambda p: -p["number"]):
        if p["status"] == "declined":
            declined.append(p)
        f = p["fields"]
        groups[p["status"]].append((f.get("topic") or f.get("domain") or "Other",
                                    problem_card(s, p, root)))
    for p in s.literature:
        st = literature.status(p)
        topic = s.topic_title(p.get("topic") or "") or "Other"
        groups[st].append(
            (topic, literature.card(p, status_badge(st) + badge(topic, "dom"), decl_href))
        )
    counts = "".join(
        f'<div class="fact st-{k}"><span class="k">{e(v)}</span>'
        f'<span class="v">{len(groups[k])}</span></div>'
        for k, v in STATUS_TITLES.items()
    )
    blurbs = {
        "proved": "Answered by a Lean theorem that settles the question, one way or the other.",
        "stuck": "Stated in Lean, but the prover is stuck. A pointer to the right Mathlib lemma is the most useful thing you can offer.",
        "formalized": "Stated in Lean, with partial results where there are any; the main question is not yet proved or refuted.",
        "accepted": "Listed, but no Lean statement of the question yet.",
    }
    def section(sid: str, title: str, n: int, blurb: str, inner: str) -> str:
        # Each group folds under its heading; the cards carry their own topic.
        return (
            f'<section class="pgroup" id="{sid}"><details open>'
            f'<summary class="shead"><h2>{e(title)}</h2><span class="n">{n}</span></summary>'
            f'<p class="small">{blurb}</p>{inner}</details></section>'
        )

    secs = []
    for k in ("proved", "stuck", "formalized", "accepted"):
        items = groups[k]
        if items:
            secs.append(section(k, STATUS_TITLES[k], len(items), e(blurbs[k]),
                                "".join(html_ for _, html_ in items)))
    if groups["pending"]:
        n = len(groups["pending"])
        secs.append(
            f'<p class="note">{n} submission{"s" if n != 1 else ""} '
            f'<a href="{e(s.pending_url())}">awaiting review on GitHub</a>. '
            "Submissions appear here once a maintainer has read them: every attempt "
            "costs tokens, and the site does not republish unreviewed text.</p>"
        )
    if declined:
        items = "".join(
            f'<li><a href="{e(p["url"])}">#{p["number"]} {e(p["title"])}</a></li>'
            for p in declined
        )
        secs.append(
            f'<details class="declined"><summary>Declined ({len(declined)})</summary>'
            f'<p class="small">Out of scope, ill-posed or duplicated. The reason is on each issue.</p>'
            f'<ul class="list">{items}</ul></details>'
        )

    # A statement that belongs to a listed problem is shown on that problem's card.
    listed = {l["node"] for p in s.literature for l in p.get("links") or []}
    loose = [n for n in s.open if n.get("problem") is None and n["name"] not in listed]
    if loose:
        cards = "".join(
            f'<article class="card"><div class="card-top"><code class="decl">{e(n["name"])}</code>'
            f'<span class="badges">{status_badge("stuck" if n["status"] == "stuck" else "formalized")}'
            f'{badge(s.topic_title(n["topic"]), "dom")}</span></div>'
            + (f'<p class="prose">{e(n["informal"])}</p>' if n["informal"] else "")
            + f'<pre class="sig lean">{highlight_lean(n["statement"])}</pre></article>'
            for n in loose
        )
        secs.append(section(
            "unproved", "Other Unproved Lean Statements", len(loose),
            "Statements in the knowledgebase that Lean has checked as well-formed but "
            "nobody has proved, and that belong to none of the problems above: the "
            "machine's own conjectures and the steps it filed towards other results. "
            f'If you can see how to prove one, say so in <a href="{e(s.discussions())}">'
            "the discussions</a>.", cards))
    body = f"""
<header class="phead" id="submit">
  <p class="eyebrow">From papers, books and you</p>
  <h1>Open Problems</h1>
  <p class="lead full">Open problems the machine works on, from papers and books or
  submitted by you. A problem counts as settled when a Lean theorem answers it,
  one way or the other, and that theorem has passed the round trip.</p>
  <div class="cta"><a class="btn primary" href="{e(s.new_problem())}">Submit a problem</a></div>
  {submit_guide(s)}
</header>
<div class="facts">{counts}</div>
{"".join(secs)}
"""
    return page(s, title="Open Problems", root=root, active="problems/", body=body, math=True)


def render_problem(s: Site, p: dict) -> str:
    root = "../../"
    f = p["fields"]
    parts = [
        f'<nav class="crumbs"><a href="{root}problems/">Open Problems</a> / #{p["number"]}</nav>',
        f'<header class="phead"><h1>{e(p["title"])}</h1><div class="badges">'
        f'{status_badge(p["status"])}'
        + (badge(f["domain"], "dom") if f.get("domain") else "")
        + (badge(f["kind"], "dom") if f.get("kind") else "")
        + "</div>"
        f'<p class="small">Posed by <a href="https://github.com/{e(p["author"])}">@{e(p["author"])}</a> '
        f'on {e(day(p["created_at"]))} · <a href="{e(p["url"])}">issue #{p["number"]}</a> '
        f'({p["comments"]} comment{"s" if p["comments"] != 1 else ""})</p></header>',
        f'<h2>Statement</h2><div class="prose big math pre-wrap">{e(f.get("statement", ""))}</div>',
    ]
    if f.get("topic"):
        parts.append(f'<p class="small">Topic: {e(f["topic"])}</p>')
    if f.get("references"):
        parts.append(f'<h2>References</h2><div class="prose pre-wrap">{e(f["references"])}</div>')
    if f.get("lean"):
        parts.append(
            "<h2>Lean suggested by the submitter</h2>"
            '<p class="small">Reference only. It has not been checked, and the '
            "statement in the knowledgebase is written and verified independently.</p>"
            f'<pre>{e(f["lean"])}</pre>'
        )
    answered = s.answers.get(p["number"], [])
    if answered:
        cards = []
        for n in answered:
            d = s.by_name.get(n["name"])
            if d:
                cards.append(decl_card(s, d, root))
            else:
                cards.append(
                    f'<article class="card"><div class="card-top"><code class="decl">{e(n["name"])}</code>'
                    f'<span class="badges">{status_badge("stuck" if n.get("status") == "stuck" else "formalized")}</span></div>'
                    f'<pre class="sig lean">{highlight_lean(n["statement"])}</pre></article>'
                )
        parts.append("<h2>In the knowledgebase</h2>" + "".join(cards))
    parts.append(
        f'<div class="actions"><a class="btn" href="{e(p["url"])}">Discuss on the issue</a></div>'
    )
    return page(
        s,
        title=f'#{p["number"]} {p["title"]}',
        root=root,
        active="problems/",
        body="".join(parts),
        math=True,
        description=clip(f.get("statement", ""), 180),
    )


def submit_guide(s: Site) -> str:
    """How submitting works, one paragraph folded under the Submit button at
    the top of the Problems page. The old submit/ address lands on #submit,
    which opens it."""
    return f"""<details class="submit-guide" id="submit-guide">
  <summary>How submitting works</summary>
  <p class="small">Submit one precise statement as a GitHub issue; Lean is
  optional. Once a maintainer accepts it, the machine states it in Lean, checks
  that the statement says what you said, and tries to prove it. A proved problem
  appears here, credited to you. To dispute a result,
  <a href="{e(s.new_verdict())}">open a challenge</a>; for anything else, use
  <a href="{e(s.discussions())}">the discussions</a>.</p>
</details>
<script>if (location.hash === "#submit") document.getElementById("submit-guide").open = true;</script>
"""


def week_span(r: dict) -> str:
    a = time.strptime(r["start"], "%Y-%m-%d")
    b = time.strptime(r["end"], "%Y-%m-%d")
    if r.get("period") == "month":
        return time.strftime("%B %Y", a)
    if a.tm_mon == b.tm_mon:
        return f"{a.tm_mday}–{b.tm_mday} {time.strftime('%b %Y', b)}"
    return f"{a.tm_mday} {time.strftime('%b', a)} – {b.tm_mday} {time.strftime('%b %Y', b)}"


def weekly_highlights(r: dict) -> list[dict]:
    return [x for f in r["fields"] for x in f["results"] if x.get("highlight")]


def outcome_badge(r: dict, x: dict) -> str:
    label = (r.get("outcomes") or {}).get(x["outcome"], x["outcome"].title())
    return badge(label, f"wk-{x['outcome']}")


def report_months(r: dict) -> list[str]:
    """The calendar months a report covers, as YYYY-MM: a week can straddle two."""
    a, b = r["start"][:7], r["end"][:7]
    return [a] if a == b else [a, b]


def render_reports(s: Site) -> str:
    """Every summary report in one list, newest first, each tagged by its
    period, with a search box and filters for the period and the month. app.js
    does the filtering; without JavaScript the whole list shows."""
    root = "../"
    reports = sorted(
        [(p, r) for p in PERIODS for r in s.reports(p)],
        key=lambda pr: (pr[1]["end"], pr[0] == "month"), reverse=True,
    )

    def item(period: str, r: dict) -> str:
        P = PERIODS[period]
        hls = weekly_highlights(r)
        hay = searchable(r["title"], r.get("summary", ""), r["week"], week_span(r),
                         *(x["headline"] for x in hls))
        return (
            f'<article class="news-item rp" id="{e(period)}-{e(r["week"])}" '
            f'data-period="{period}" data-months="{" ".join(report_months(r))}" '
            f'data-q="{e(hay)}">'
            f'<p class="news-when">{badge(P["tag"], f"rp-{period}")}<span>{e(r["week"])}</span>'
            f'<span class="small">{e(week_span(r))}</span>'
            f'<span class="small">{r.get("minutes", "?")} min read</span></p>'
            f'<div class="news-main"><h3><a href="{root}{P["dir"]}/{e(r["week"])}/">'
            f'{e(r["title"])}</a></h3>'
            f'<p class="prose">{e(r.get("summary", ""))}</p>'
            + "".join(f'<p class="wk-hl">{outcome_badge(r, x)} {e(x["headline"])}</p>'
                      for x in hls)
            + "</div></article>"
        )

    items = "".join(item(p, r) for p, r in reports)
    months = sorted({m for _, r in reports for m in report_months(r)}, reverse=True)
    month_opts = "".join(
        f'<option value="{m}">{time.strftime("%B %Y", time.strptime(m, "%Y-%m"))}</option>'
        for m in months
    )
    seg = "".join(
        f'<button type="button" data-period="{k}" aria-pressed="{"true" if k == "all" else "false"}">'
        f"{v}</button>"
        for k, v in [("all", "All"), *((p, P["tag"]) for p, P in PERIODS.items())]
    )
    toolbar = f"""
  <div class="toolbar">
    <div class="search">
      <label class="vh" for="rq">Search the reports</label>
      <input id="rq" type="search" placeholder="Search the reports" autocomplete="off">
      <kbd aria-hidden="true">/</kbd>
    </div>
    <div class="controls">
      <div class="seg" role="group" aria-label="Period">{seg}</div>
      <label class="vh" for="r-month">Month</label>
      <select id="r-month"><option value="all">Any time</option>{month_opts}</select>
    </div>
  </div>
  <p class="rcount"><span id="r-count" aria-live="polite">{_n_reports(len(reports))}</span>
  <button type="button" class="linkish" id="r-clear" hidden>Clear filters</button></p>"""
    body = f"""
<header class="phead">
  <p class="eyebrow">What Lean accepted, period by period</p>
  <h1>Summary Reports</h1>
  <p class="lead full">The theorems Lean accepted over a week or a month, told in about
  ten minutes: what was settled, in which fields, from which papers, and what is
  still open. Every theorem a report names links to its Lean proof.</p>
</header>
<section class="rp-wrap" id="reports">
  {toolbar if reports else ""}
  {f'<div class="news-list" id="r-list">{items}</div>' if items else '<p class="prose">No report yet.</p>'}
  <p class="prose" id="r-empty" hidden>No report matches.
  <button type="button" class="linkish" data-clear>Clear filters</button></p>
</section>"""
    return page(s, title="Summary Reports", root=root, active="reports/", body=body,
                script=bool(reports),
                description="What Lean accepted each week and each month, in ten minutes.")


def _n_reports(k: int) -> str:
    return f"{k} report{'s' if k != 1 else ''}"


def render_weekly(s: Site, i: int, period: str = "week") -> str:
    """One week (or month), laid out for a ten-minute read: the week in one
    minute, every result at a glance, then one card per result by field, what
    is still open and the terms. The reports are newest first, so the previous
    week is the next item."""
    P = PERIODS[period]
    reports = s.reports(period)
    r = reports[i]
    root = "../../"
    n = 0
    anchors: list[tuple[dict, dict, str]] = []
    for f in r["fields"]:
        for x in f["results"]:
            n += 1
            anchors.append((f, x, f"r{n}"))
    aid = {id(x): a for _, x, a in anchors}

    hl = "".join(
        f'<li>{outcome_badge(r, x)} <a href="#{aid[id(x)]}">{e(x["headline"])}</a></li>'
        for x in weekly_highlights(r)
    )
    rows, last = [], None
    for f, x, a in anchors:
        if f is not last:
            rows.append(f'<tr class="wk-field"><th colspan="3" scope="colgroup">'
                        f'{e(f["name"])}</th></tr>')
            last = f
        rows.append(
            f'<tr><td><a href="#{a}">{e(x["headline"])}</a></td>'
            f"<td>{outcome_badge(r, x)}</td>"
            f'<td class="mono">{e(x.get("source") or "—")}</td></tr>'
        )
    rows = "".join(rows)

    def card(x: dict, a: str) -> str:
        src = x.get("source") or ""
        links = []
        if src:
            links.append(f'<a href="https://arxiv.org/abs/{e(src.removeprefix("arXiv:"))}">'
                         f"{e(src)} &rarr;</a>")
        links.append(f'<a href="{root}d/{slug(x["main"])}/">Lean: '
                     f'<span class="mono">{e(x["main"])}</span> &rarr;</a>')
        rest = [d for d in x["declarations"] if d != x["main"]]
        more = (
            f'<details class="news-more"><summary>{len(rest)} supporting '
            f'theorem{"s" if len(rest) != 1 else ""}</summary>'
            f'<div class="news-decls">{related(s, rest, root)}</div></details>'
            if rest else ""
        )
        # A formalization is the paper's result: the card says what is checked,
        # not what "we showed".
        shown = "What is checked" if x["outcome"] == "formalized" else "What we showed"
        rowsd = [("The question", x["question"]), (shown, x["answer"]),
                 ("Why it matters", x["why"])]
        if x.get("idea"):
            rowsd.append(("The idea", x["idea"]))
        dl = "".join(f"<dt>{k}</dt><dd>{e(v)}</dd>" for k, v in rowsd)
        return (
            f'<article class="wk-card" id="{a}">'
            f'<p class="badges">{outcome_badge(r, x)}</p>'
            f'<h3>{e(x["headline"])}</h3><dl class="wk-dl">{dl}</dl>'
            f'<p class="news-links">{"".join(links)}</p>{more}</article>'
        )

    secs = []
    for f in r["fields"]:
        cards = "".join(card(x, aid[id(x)]) for x in f["results"])
        secs.append(f'<h2>{e(f["name"])}</h2><p>{e(f.get("context", ""))}</p>{cards}')
    if r.get("outlook"):
        secs.append("<h2>Still open</h2><ul>"
                    + "".join(f"<li>{e(x)}</li>" for x in r["outlook"]) + "</ul>")
    if r.get("glossary"):
        secs.append('<h2>Terms</h2><dl class="wk-terms">'
                    + "".join(f'<dt>{e(g["term"])}</dt><dd>{e(g["meaning"])}</dd>'
                              for g in r["glossary"]) + "</dl>")

    def side(x: dict | None, cls: str, label: str) -> str:
        if not x:
            return f'<span class="{cls}"></span>'
        return (
            f'<a class="{cls}" href="{root}{P["dir"]}/{e(x["week"])}/"><span class="small">{label}</span>'
            f'<span class="mono">{e(x["week"])}</span></a>'
        )

    older = reports[i + 1] if i + 1 < len(reports) else None
    newer = reports[i - 1] if i > 0 else None
    noun = P["noun"]
    pager = (
        f'<nav class="pager" aria-label="{P["tag"]} reports">'
        f'{side(older, "prev", f"&larr; Earlier {noun}")}'
        f'<a class="pos" href="{root}reports/"><span class="small">All reports</span></a>'
        f'{side(newer, "next", f"Later {noun} &rarr;")}</nav>'
    )
    partial = f" (so far: the {noun} is not over)" if r.get("partial") else ""
    body = f"""
<header class="phead">
  <p class="eyebrow">{P["tag"]} report &middot; {e(r["week"])} &middot; {e(week_span(r))}{partial}
  &middot; {r.get("minutes", "?")} min read</p>
  <h1>{e(r["title"])}</h1>
</header>
<section class="wk">
  <div class="wk-minute">
    <p class="wk-label">The {noun} in one minute</p>
    <p class="wk-sum">{e(r.get("summary", ""))}</p>
    <ul class="wk-hls">{hl}</ul>
    <p class="wk-num">{e(r.get("numbers", ""))}</p>
  </div>
  <h2>At a glance</h2>
  <div class="wk-table-wrap"><table class="wk-table">
    <thead><tr><th>Result</th><th>Outcome</th><th>Paper</th></tr></thead>
    <tbody>{rows}</tbody></table></div>
  {"".join(secs)}
  <p class="small"><em>{e(r.get("disclaimer", ""))}</em></p>
  {pager}
</section>"""
    return page(s, title=f"{P['tag']} report {r['week']}", root=root, active="reports/",
                body=body, description=r.get("summary", ""))


def render_moved(s: Site, to: str) -> str:
    """A page that has moved: it forwards to its new address, keeping the
    query and the anchor so a shared, filtered link still lands where it
    pointed. Without JavaScript the refresh still goes to the right page.
    When the new address is itself an anchor, the link's own anchor wins."""
    url = f"../{to}"
    path, _, frag = url.partition("#")
    frag = "#" + frag if frag else ""
    canonical = s.cfg.get("base_url", "").rstrip("/") + "/" + to
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Moved · {NAME}</title>
<meta name="robots" content="noindex">
<link rel="canonical" href="{e(canonical)}">
<meta http-equiv="refresh" content="0; url={e(url)}">
<script>location.replace({json.dumps(path)} + location.search + (location.hash || {json.dumps(frag)}));</script>
</head>
<body><p>This page is now at <a href="{e(url)}">{e(canonical)}</a>.</p></body>
</html>
"""


def render_404(s: Site) -> str:
    # GitHub Pages serves 404.html for every depth, so its links are absolute.
    base = s.cfg.get("base_url", "").rstrip("/") + "/"
    body = (
        '<header class="phead"><h1>Not here</h1><p class="lead">That page does not '
        "exist. A declaration that was renamed keeps no forwarding address; search "
        f'the <a href="{e(base)}knowledgebase/">knowledgebase</a> for it.</p></header>'
    )
    return page(s, title="Not found", root=base, active="", body=body)


# --------------------------------------------------------------------- chat
# The chat page (experimental) runs in the reader's browser with the reader's
# own API key. The model reads the knowledgebase through two tools that
# static/chat.js answers from these files: a search index of everything the
# site lists, and the long fields of each declaration, fetched only when the
# model asks for one.
CHAT_INDEX = "chat/kb-index.json"
CHAT_DETAIL = "chat/kb-detail.json"
CHAT_STATEMENT = 1500  # characters of a Lean statement kept in the index


def chat_data(s: Site) -> tuple[dict, dict]:
    entries = []
    for d in s.decls:
        entries.append({
            "type": "declaration",
            "name": d["name"],
            "kind": d["kind"],
            "status": ("definition" if d["is_def"] else
                       "verified in Lean" if s.verified(d) else "uses untrusted axioms"),
            "domain": s.domain_title(d["domain"]),
            "topic": s.topic_title(d["topic"]),
            "informal": d.get("informal") or "",
            "statement": (d.get("statement") or "")[:CHAT_STATEMENT],
            "provenance": PROVENANCE.get(d.get("provenance") or "", ("",))[0],
            "citation": d.get("citation") or "",
            "problem": d.get("problem"),
            "url": f"d/{slug(d['name'])}/",
        })
    for n in s.open:
        entries.append({
            "type": "declaration",
            "name": n["name"],
            "kind": n.get("kind") or "theorem",
            "status": "stated in Lean, not yet proved",
            "domain": s.domain_title(n.get("domain") or ""),
            "topic": s.topic_title(n.get("topic") or ""),
            "informal": n.get("informal") or "",
            "statement": (n.get("statement") or "")[:CHAT_STATEMENT],
            "provenance": "",
            "citation": n.get("citation") or "",
            "problem": n.get("problem"),
            "url": f"knowledgebase/?q={quote(n['name'])}&kind=open",
        })
    for p in s.literature:
        entries.append({
            "type": "open_problem",
            "name": p["ref"],
            "title": p["title"],
            "status": STATUS_TITLES[literature.status(p)],
            "domain": s.domain_title(p.get("domain") or ""),
            "topic": s.topic_title(p.get("topic") or ""),
            "statement": p.get("statement") or "",
            "source": ", ".join(x for x in (p.get("source"), p.get("location")) if x),
            "source_title": p.get("source_title") or "",
            "known": p.get("rationale") or "",
            "lean": [{"name": l["node"], "role": l["role"]} for l in p.get("links") or []],
            "url": f"problems/#{quote(p['ref'])}",
        })
    for p in s.problems:
        if p["status"] in ("pending", "declined"):
            continue  # unreviewed or declined submissions are never published
        entries.append({
            "type": "community_problem",
            "name": f"#{p['number']}",
            "title": p["title"],
            "status": STATUS_TITLES.get(p["status"], p["status"]),
            "domain": p["fields"].get("domain") or "",
            "topic": p["fields"].get("topic") or "",
            "statement": p["fields"].get("statement") or "",
            "lean": [{"name": n["name"], "role": "answer"}
                     for n in s.answers.get(p["number"], [])],
            "url": f"problems/{p['number']}/",
        })
    t = s.kb["totals"]
    index = {
        "generated": s.kb["generated"],
        "trusted_axioms": s.kb["trusted_axioms"],
        "totals": {k: t[k] for k in ("declarations", "theorems", "definitions", "topics")
                   if k in t},
        "domains": [
            {"title": dm["title"],
             "topics": [tp["title"] for tp in dm["topics"]]}
            for dm in s.kb["domains"]
        ],
        "entries": entries,
    }
    detail = {
        d["name"]: {
            "source": d.get("source") or "",
            "reading": d.get("reading") or "",
            "explanation": d.get("explanation") or "",
            "deps": d.get("deps") or [],
            "used_by": d.get("used_by") or [],
            "axioms": d.get("axioms") or [],
            "lean_path": d.get("lean_path") or "",
            "source_url": s.blob(d["lean_path"]) if d.get("lean_path") else "",
        }
        for d in s.decls
    }
    return index, detail


def render_chat(s: Site) -> str:
    root = "../"
    t = s.kb["totals"]
    body = f"""
<header class="phead">
  <nav class="crumbs"><a href="{root}knowledgebase/#graph">Knowledgebase</a> / Chat</nav>
  <p class="eyebrow">Experimental</p>
  <h1>Chat with Knowledgebase</h1>
  <p class="lead full">Ask in plain words about the {t["declarations"]} declarations, the
  open problems and what Lean has settled. The model searches the knowledgebase for
  you, links every entry it uses, and can search the web for what the knowledgebase
  does not cover. It runs on your own API key.</p>
</header>
<aside class="note chat-privacy" aria-label="Your API key">
  <p><strong>We do not collect your API key.</strong> AFTD has no server behind this
  page: it runs in your browser, and your key goes only to the provider you choose,
  straight from your browser over HTTPS. Your key, your questions and the answers are
  never sent to us, stored by us or logged by us. You can check this in
  <a href="{e(s.blob("web/static/chat.js"))}">the page&rsquo;s code</a>.</p>
</aside>
<div class="chat" id="chat" data-index="{root}{CHAT_INDEX}" data-detail="{root}{CHAT_DETAIL}">
  <details class="card chat-set" id="chat-set" open>
    <summary><span class="chat-set-h">Model and key</span>
    <span class="small" id="chat-set-sum"></span></summary>
    <div class="chat-grid">
      <label>Provider
        <select id="chat-provider">
          <option value="gemini">Google Gemini</option>
          <option value="anthropic">Anthropic Claude</option>
          <option value="openai">OpenAI</option>
          <option value="openrouter">OpenRouter (many vendors, one key)</option>
          <option value="deepseek">DeepSeek</option>
        </select></label>
      <label>Model <select id="chat-model"></select></label>
      <label class="wide" id="chat-other-row" hidden>Model id
        <input id="chat-other" type="text" spellcheck="false" autocomplete="off"
               placeholder="Any model id the provider offers"></label>
      <label class="wide">API key
        <input id="chat-key" type="password" spellcheck="false" autocomplete="off"
               placeholder="Paste your key; it stays in your browser"></label>
    </div>
    <div class="chat-opts">
      <label class="switch" id="chat-web-row"><input type="checkbox" id="chat-web" checked> Search the web too</label>
      <label class="switch"><input type="checkbox" id="chat-remember"> Remember the key on this device</label>
      <a class="small" id="chat-keylink" href="#" target="_blank" rel="noopener noreferrer">Get a key</a>
    </div>
    <p class="small">The provider bills your account for what you ask. Unless you tick
    <em>Remember</em>, the key is kept only in this tab and forgotten when you close it;
    with <em>Remember</em> it stays in this browser, on this device, until you clear it.
    Answers come from a language model: check what it says against the linked entries,
    and treat only an entry marked <em>verified in Lean</em> as proved.</p>
  </details>
  <section class="chat-log" id="chat-log" aria-live="polite">
    <div class="chat-empty" id="chat-empty">
      <p class="prose">Try one of these, or ask your own question.</p>
      <div class="chat-starters">
        <button type="button" class="chip">What has been proved here about envy-free allocation of chores?</button>
        <button type="button" class="chip">Which open problems from the literature are settled in Lean, and how?</button>
        <button type="button" class="chip">Explain the Lean statement of condorcet_winner_unique and what it depends on.</button>
        <button type="button" class="chip">What is the best known approximation for maximin share allocations, and which parts of it are in the knowledgebase?</button>
      </div>
    </div>
  </section>
  <form class="chat-form" id="chat-form">
    <label class="vh" for="chat-q">Your question</label>
    <textarea id="chat-q" rows="2" placeholder="Ask about a theorem, a topic or an open problem"></textarea>
    <div class="chat-acts">
      <button type="button" class="linkish" id="chat-new">New chat</button>
      <span class="small" id="chat-usage"></span>
      <button type="submit" class="btn primary" id="chat-send">Ask</button>
    </div>
  </form>
</div>
<script defer src="{root}static/chat.js"></script>
"""
    return page(
        s,
        title="Chat with Knowledgebase",
        root=root,
        active="knowledgebase/",
        body=body,
        math=True,
        description="Chat with the AFTD knowledgebase, with your own API key (experimental).",
    )


# -------------------------------------------------------------------- build
def build(
    kb: dict,
    issues: list[dict],
    cfg: dict,
    out: Path,
    news: list[dict] | None = None,
    weekly: list[dict] | None = None,
    monthly: list[dict] | None = None,
) -> dict[str, int]:
    s = Site(kb, issues, cfg, news, weekly, monthly)
    if out.exists():
        shutil.rmtree(out)
    shutil.copytree(HERE / "static", out / "static")

    def write(rel: str, text: str) -> None:
        path = out / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    write("index.html", render_home(s))
    write("knowledgebase/index.html", render_kb(s))
    write("results/index.html", render_moved(s, "knowledgebase/"))
    write("problems/index.html", render_problems(s))
    write("submit/index.html", render_moved(s, "problems/#submit"))
    write("news/index.html", render_moved(s, "#news"))
    write("reports/index.html", render_reports(s))
    write("weekly/index.html", render_moved(s, "reports/"))
    for period, P in PERIODS.items():
        for i, r in enumerate(s.reports(period)):
            write(f"{P['dir']}/{r['week']}/index.html", render_weekly(s, i, period))
    write("chat/index.html", render_chat(s))
    index, detail = chat_data(s)
    write(CHAT_INDEX, json.dumps(index, ensure_ascii=False, separators=(",", ":")))
    write(CHAT_DETAIL, json.dumps(detail, ensure_ascii=False, separators=(",", ":")))
    write("404.html", render_404(s))
    for d in s.decls:
        write(f"d/{slug(d['name'])}/index.html", render_decl(s, d))
    published = [p for p in s.problems if p["status"] not in ("pending", "declined")]
    for p in published:
        write(f"problems/{p['number']}/index.html", render_problem(s, p))
    # Pages would otherwise run Jekyll over the output and drop nothing useful,
    # but it is slower and ignores directories that start with an underscore.
    write(".nojekyll", "")
    return {
        "declarations": len(s.decls),
        "problems": len(published),
        "news": len(s.news),
        "weekly": len(s.weekly),
        "monthly": len(s.monthly),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", default="_site")
    ap.add_argument("--kb", default=str(HERE / "data" / "kb.json"))
    ap.add_argument("--problems", default=str(HERE / "data" / "problems.json"))
    ap.add_argument("--config", default=str(HERE / "site.json"))
    ap.add_argument("--news", default=str(HERE / "news.json"))
    ap.add_argument("--weekly", default=str(HERE / "weekly"))
    ap.add_argument("--monthly", default=str(HERE / "monthly"))
    args = ap.parse_args()
    kb = json.loads(Path(args.kb).read_text(encoding="utf-8"))
    cfg = json.loads(Path(args.config).read_text(encoding="utf-8"))
    pp = Path(args.problems)
    issues = json.loads(pp.read_text(encoding="utf-8"))["issues"] if pp.is_file() else []
    news_path = Path(args.news)
    news = (
        json.loads(news_path.read_text(encoding="utf-8"))["entries"] if news_path.is_file() else []
    )
    def reports(d: str) -> list[dict]:
        p = Path(d)
        return [json.loads(f.read_text(encoding="utf-8"))
                for f in sorted(p.glob("*.json"))] if p.is_dir() else []

    n = build(kb, issues, cfg, Path(args.out), news, reports(args.weekly),
              reports(args.monthly))
    print(
        f"wrote {args.out}  ({n['declarations']} declaration pages, "
        f"{n['problems']} problem pages, {n['news']} news entries, "
        f"{n['weekly']} weekly and {n['monthly']} monthly reports)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
