#!/usr/bin/env python3
"""Build the public AFTD site from the knowledge-base snapshot and the issues.

    python3 web/build.py --out _site

Inputs, all under `web/`:

* `data/kb.json` -- written by `scripts/snapshot.py` on the machine that runs
  the loop, and committed. Every declaration the site shows comes from here.
* `data/problems.json` -- written by `fetch_problems.py` from GitHub issues at
  build time. Optional: without it the site simply has no community problems.
* `site.json` -- the repository and branch that every outbound link points at.

Pages:

    index.html                  what this is, what is new, where to start
    results/                    every verified declaration, searchable
    d/<name>/                   one declaration: statement, proof, dependencies,
                                the problem it answers, challenges against it
    problems/                   community problems by status, and what is open
    problems/<number>/          one reviewed problem and what answers it
    submit/                     how to submit a problem or challenge a result

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

from problems import PROBLEM_LABEL, STATUSES, VERDICT_LABEL, status  # noqa: E402

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

    def __init__(self, kb: dict, issues: list[dict], cfg: dict):
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
        # Each topic's declarations in the order the results page lists them,
        # for the previous/next links on a declaration page.
        self.in_topic: dict[str, list[dict]] = {}
        for d in self.decls:
            self.in_topic.setdefault(d["topic"], []).append(d)

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
NAV = [("results/", "Results"), ("problems/", "Problems"), ("submit/", "Submit")]


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
      <a href="{root}results/">Verified results</a>
      <a href="{root}problems/">Community problems</a>
      <a href="{root}submit/">Submit a problem</a>
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
    """Text as the results search sees it: lower case, with Lean's `_` and `.`
    as spaces, so "condorcet unique" finds `condorcet_winner_unique`. app.js
    normalises the query the same way."""
    return " ".join(re.sub(r"[_.\s]+", " ", " ".join(texts).lower()).split())


def inline_code(text: str) -> str:
    """Escaped text with `backticked` spans set as code, the way the models
    write Lean names into their prose."""
    return re.sub(r"`([^`\n]+)`", r"<code>\1</code>", e(text))


def kind_badge(d: dict) -> str:
    return badge(d["kind"], "kind def" if d["is_def"] else "kind thm")


def decl_card(s: Site, d: dict, root: str, *, sig: bool = True) -> str:
    """One declaration in a list: what it says in words first, the Lean name
    and signature second, and the whole card is the link to the rest."""
    tags = [kind_badge(d)]
    if d.get("provenance") == "original":
        tags.append(badge("original", "orig", "Proposed by the machine, not transcribed from the literature"))
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
            f'<a href="results/#d-{e(d["name"])}">{e(d["title"])}</a>'
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
        <a class="btn primary" href="submit/">Submit a problem</a>
        <a class="btn" href="results/">Browse {t["declarations"]} results</a>
      </div>
    </div>
    <div class="hero-card">{proof_window(s, featured(s), root)}</div>
  </div>
</section>

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
    <a href="submit/">How submitting works &rarr;</a></div>
    <div class="panel"><span class="panel-n">02</span><h3>Read the proofs</h3>
    <p>Every verified declaration has its own page: the statement in words and in
    Lean, the full proof, what it builds on and what builds on it.</p>
    <a href="results/">All results &rarr;</a></div>
    <div class="panel"><span class="panel-n">03</span><h3>Judge the verdicts</h3>
    <p>Correctness is settled by Lean. Everything else is yours to dispute: a name
    that claims too much, a trivial statement, a definition the subject would not
    recognise.</p>
    <a href="{e(s.new_verdict())}">Challenge a result &rarr;</a></div>
  </div>
</section>

<section class="wrap band split">
  <div>
    <header class="shead"><h2>Community problems</h2><a href="problems/">All problems &rarr;</a></header>
    {probs}
  </div>
  <div>
    <header class="shead"><h2>Recently verified</h2><a href="results/">All results &rarr;</a></header>
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
    <p>It is not an attempt on open problems, and not a claim that mathematicians
    are replaceable. Most of the knowledge base is known mathematics, carefully
    transcribed and machine-checked, plus a growing minority of modest original
    statements. The value is in the aggregate &mdash; verified, open and
    cumulative &mdash; not in any single line of it.</p>
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


def render_results(s: Site) -> str:
    root = "../"
    by_dom: dict[str, dict[str, list[dict]]] = {}
    for d in s.decls:
        by_dom.setdefault(d["domain"], {}).setdefault(d["topic"], []).append(d)
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
            target = (s.topics.get(tname) or {}).get("target") or 0
            bar = ""
            if target:
                pct = min(100, round(100 * len(ds) / target))
                bar = (
                    f'<span class="meter" title="{len(ds)} of a target of {target}">'
                    f'<span style="width:{pct}%"></span></span>'
                    f'<span class="tnum">{len(ds)} of {target} targeted</span>'
                )
            blocks.append(
                f'<section class="topic" id="t-{e(tname)}"><header class="thead">'
                f"<h3>{e(s.topic_title(tname))}</h3>{bar}</header>"
                + "".join(decl_card(s, d, root) for d in ds)
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
  <p class="eyebrow">The knowledge base</p>
  <h1>Verified results</h1>
  <p class="lead">{t["declarations"]} declarations &mdash; {t["theorems"]} theorems and
  {t["definitions"]} definitions in {t["topics"]} topics &mdash; each elaborated by
  Lean&nbsp;4 against Mathlib, with nothing outside the trusted axioms. Open one for
  its proof, what it builds on and what builds on it.</p>
</header>
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
    <div id="results" class="rlist grouped">
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
        title="Verified results",
        root=root,
        active="results/",
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


def render_decl(s: Site, d: dict) -> str:
    root = "../../"
    badges = [kind_badge(d)]
    if s.verified(d):
        badges.append(badge("verified", "ok", "Lean accepted it, and #print axioms lists only trusted axioms"))
    if d.get("provenance") == "original":
        badges.append(badge("original", "orig", "Proposed by the machine, not transcribed from the literature"))
    parts = [
        f'<nav class="crumbs"><a href="{root}results/">Results</a> / '
        f'<a href="{root}results/#d-{e(d["domain"])}">{e(s.domain_title(d["domain"]))}</a> / '
        f'<a href="{root}results/#t-{e(d["topic"])}">{e(s.topic_title(d["topic"]))}</a></nav>',
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
        f'<a class="btn" href="{e(s.discussions(d["name"]))}">Discuss this result</a>'
        f'<a class="btn" href="{e(s.new_verdict(d["name"]))}">Challenge it</a></div>'
    )
    parts.append(pager(s, d, root))
    return page(
        s,
        title=d["name"],
        root=root,
        active="results/",
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
    if d.get("citation"):
        rows.append(("Source", e(d["citation"])))
    elif d.get("provenance") == "original":
        rows.append(("Source", "Proposed by the machine; not transcribed from the literature"))
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
    """Previous and next in the same topic, in results-page order."""
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
    root = "../"
    groups: dict[str, list[dict]] = {k: [] for k in STATUSES}
    for p in sorted(s.problems, key=lambda p: -p["number"]):
        groups[p["status"]].append(p)
    counts = "".join(
        f'<div class="fact st-{k}"><span class="k">{e(v)}</span>'
        f'<span class="v">{len(groups[k])}</span></div>'
        for k, v in STATUSES.items()
    )
    blurbs = {
        "proved": "Formalized, checked against the English, and proved.",
        "stuck": "Formalized, but the prover is stuck. A pointer to the right Mathlib lemma is the most useful thing you can offer.",
        "formalized": "The statement is in the knowledge base and waiting for its proof.",
        "accepted": "Reviewed and queued. The machine has not formalized it yet.",
    }
    secs = []
    for k in ("proved", "stuck", "formalized", "accepted"):
        if not groups[k]:
            continue
        secs.append(
            f'<section class="pgroup" id="{k}"><header class="shead"><h2>{e(STATUSES[k])}</h2>'
            f'<span class="n">{len(groups[k])}</span></header><p class="small">{e(blurbs[k])}</p>'
            + "".join(problem_card(s, p, root) for p in groups[k])
            + "</section>"
        )
    if not secs:
        secs.append(
            '<p class="empty">No reviewed problems yet. '
            f'<a href="{e(s.new_problem())}">Submit the first one.</a></p>'
        )
    if groups["pending"]:
        n = len(groups["pending"])
        secs.append(
            f'<p class="note">{n} submission{"s" if n != 1 else ""} '
            f'<a href="{e(s.pending_url())}">awaiting review on GitHub</a>. '
            "Submissions appear here once a maintainer has read them: every attempt "
            "costs tokens, and the site does not republish unreviewed text.</p>"
        )
    if groups["declined"]:
        items = "".join(
            f'<li><a href="{e(p["url"])}">#{p["number"]} {e(p["title"])}</a></li>'
            for p in groups["declined"]
        )
        secs.append(
            f'<details class="declined"><summary>Declined ({len(groups["declined"])})</summary>'
            f'<p class="small">Out of scope, ill-posed or duplicated. The reason is on each issue.</p>'
            f'<ul class="list">{items}</ul></details>'
        )

    loose = [n for n in s.open if n.get("problem") is None]
    if loose:
        cards = "".join(
            f'<article class="card"><div class="card-top"><code class="decl">{e(n["name"])}</code>'
            f'<span class="badges">{status_badge("stuck" if n["status"] == "stuck" else "formalized")}'
            f'{badge(s.topic_title(n["topic"]), "dom")}</span></div>'
            + (f'<p class="prose">{e(n["informal"])}</p>' if n["informal"] else "")
            + f'<pre class="sig lean">{highlight_lean(n["statement"])}</pre></article>'
            for n in loose
        )
        secs.append(
            '<section class="pgroup" id="open"><header class="shead"><h2>Open in the knowledge base</h2>'
            f'<span class="n">{len(loose)}</span></header>'
            '<p class="small">Statements the machine posed itself and has not proved yet. '
            f'If you can see how, say so in <a href="{e(s.discussions())}">the discussions</a>.</p>'
            f"{cards}</section>"
        )
    body = f"""
<header class="phead">
  <p class="eyebrow">Open verdict by the community</p>
  <h1>Community problems</h1>
  <p class="lead">Statements submitted by people, attempted by the machine. A
  problem counts as proved when every declaration answering it has passed Lean
  and the round trip.</p>
  <div class="cta"><a class="btn primary" href="{e(s.new_problem())}">Submit a problem</a>
  <a class="btn" href="{root}submit/">How it works</a></div>
</header>
<div class="facts">{counts}</div>
{"".join(secs)}
"""
    return page(s, title="Community problems", root=root, active="problems/", body=body, math=True)


def render_problem(s: Site, p: dict) -> str:
    root = "../../"
    f = p["fields"]
    parts = [
        f'<nav class="crumbs"><a href="{root}problems/">Problems</a> / #{p["number"]}</nav>',
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
            "statement in the knowledge base is written and verified independently.</p>"
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
        parts.append("<h2>In the knowledge base</h2>" + "".join(cards))
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


def render_submit(s: Site) -> str:
    root = "../"
    doms = "".join(
        f'<li><strong>{e(d["title"])}</strong> &mdash; {e(clip(d["description"], 160))}</li>'
        for d in s.kb["domains"]
    )
    body = f"""
<header class="phead">
  <p class="eyebrow">Take part</p>
  <h1>Submit a problem</h1>
  <p class="lead">Give the machine a statement to prove. Submissions go through a
  GitHub issue, so you need a GitHub account, and the discussion of your problem
  happens there in public.</p>
  <div class="cta"><a class="btn primary" href="{e(s.new_problem())}">Open the submission form</a></div>
</header>
<section class="doc">
  <h2>What to submit</h2>
  <p>A single, precise statement from one of the domains below. The best
  candidates are results you can point to in a textbook or paper: the machine
  is very good at careful transcription and patchy at genuinely new
  mathematics. Your own conjectures are welcome; expect some of them to end up
  under <em>needs help</em>. Famous open problems are out of scope.</p>
  <ul class="doms">{doms}</ul>
  <p>Write the statement the way you would in a paper. LaTeX between
  <code>$&hellip;$</code> is rendered. If you know Lean, you may add a Lean
  statement, but you do not have to.</p>

  <h2>What happens next</h2>
  <ol class="flow">
    <li><strong>Review.</strong> A maintainer reads every submission before the
    machine spends anything on it, since every attempt costs tokens. Accepted
    problems get the <code>accepted</code> label; declined ones are closed with a
    reason. Until then a submission is only counted on this site, not shown.</li>
    <li><strong>Formalization.</strong> The machine writes its own Lean statement.
    It must type-check, pass the round trip against your English, and not reuse a
    name for something it is not. Any Lean you supplied is reference text and is
    never run as-is.</li>
    <li><strong>Proof.</strong> The prover works on it like any other node. If it
    gets stuck it splits the statement into lemmas, and the problem shows as
    <em>needs help</em>, with the exact statement it is stuck on.</li>
    <li><strong>Publication.</strong> When everything answering your problem is
    proved, it appears under <a href="{root}problems/">Problems</a> and in the
    results, with its full proof, and the issue is updated.</li>
  </ol>

  <h2>Credit</h2>
  <p>Your GitHub handle is shown on the problem as the person who posed it.
  Everything the machine produces is public and free to use; by submitting,
  you agree that your statement may be published, reformulated and built on
  by anyone.</p>

  <h2>Challenging a result</h2>
  <p>Whether a proof is correct is not up for debate: it elaborates and
  <code>#print axioms</code> is clean, or it is not on this site. Everything else
  is. If a declaration's name claims more than it proves, if a statement is
  trivial or vacuous, or if a definition is not the one the subject uses,
  <a href="{e(s.new_verdict())}">open a challenge</a>. Every declaration page
  has a button for it too.</p>

  <h2>Just want to talk?</h2>
  <p>Questions, ideas for the curriculum and results you built on top of the
  knowledge base belong in <a href="{e(s.discussions())}">the discussions</a>.</p>
</section>
"""
    return page(s, title="Submit a problem", root=root, active="submit/", body=body)


def render_404(s: Site) -> str:
    # GitHub Pages serves 404.html for every depth, so its links are absolute.
    base = s.cfg.get("base_url", "").rstrip("/") + "/"
    body = (
        '<header class="phead"><h1>Not here</h1><p class="lead">That page does not '
        "exist. A declaration that was renamed keeps no forwarding address; search "
        f'the <a href="{e(base)}results/">results</a> for it.</p></header>'
    )
    return page(s, title="Not found", root=base, active="", body=body)


# -------------------------------------------------------------------- build
def build(kb: dict, issues: list[dict], cfg: dict, out: Path) -> dict[str, int]:
    s = Site(kb, issues, cfg)
    if out.exists():
        shutil.rmtree(out)
    shutil.copytree(HERE / "static", out / "static")

    def write(rel: str, text: str) -> None:
        path = out / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    write("index.html", render_home(s))
    write("results/index.html", render_results(s))
    write("problems/index.html", render_problems(s))
    write("submit/index.html", render_submit(s))
    write("404.html", render_404(s))
    for d in s.decls:
        write(f"d/{slug(d['name'])}/index.html", render_decl(s, d))
    published = [p for p in s.problems if p["status"] not in ("pending", "declined")]
    for p in published:
        write(f"problems/{p['number']}/index.html", render_problem(s, p))
    # Pages would otherwise run Jekyll over the output and drop nothing useful,
    # but it is slower and ignores directories that start with an underscore.
    write(".nojekyll", "")
    return {"declarations": len(s.decls), "problems": len(published)}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", default="_site")
    ap.add_argument("--kb", default=str(HERE / "data" / "kb.json"))
    ap.add_argument("--problems", default=str(HERE / "data" / "problems.json"))
    ap.add_argument("--config", default=str(HERE / "site.json"))
    args = ap.parse_args()
    kb = json.loads(Path(args.kb).read_text(encoding="utf-8"))
    cfg = json.loads(Path(args.config).read_text(encoding="utf-8"))
    pp = Path(args.problems)
    issues = json.loads(pp.read_text(encoding="utf-8"))["issues"] if pp.is_file() else []
    n = build(kb, issues, cfg, Path(args.out))
    print(
        f"wrote {args.out}  ({n['declarations']} declaration pages, "
        f"{n['problems']} problem pages)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
