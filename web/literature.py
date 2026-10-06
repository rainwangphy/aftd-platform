"""Open problems from the literature: the list the machine works from.

Every entry is a question a paper, survey or book leaves open, kept in the
knowledgebase's open-problem list and exported by `scripts/snapshot.py` as
`literature` in `data/kb.json`. Each says what is known and where it was
posed; it is never called solved here unless a linked Lean theorem settles it
(`settled_in_lean`, derived by the snapshot from the proved declarations).

Stdlib only, like the rest of `web/`.
"""

from __future__ import annotations

import html
import re
from typing import Callable

e = html.escape

# The order the statuses are shown in, with the words the site uses for them.
LIT_STATUSES = {
    "settled_in_lean": "Settled in Lean",
    "formalized": "Stated in Lean",
    "open": "Open",
    "reported_solved": "Reported solved",
}
_BADGE = {
    "settled_in_lean": "st-proved",
    "formalized": "st-formalized",
    "open": "st-unproved",
    "reported_solved": "st-accepted",
}
_ARXIV = re.compile(r"arXiv:\s*(\d{4}\.\d{4,5})", re.I)


def source_html(src: str) -> str:
    """The source as text, with every arXiv id linked to its abstract page."""
    out, last = [], 0
    for m in _ARXIV.finditer(src):
        out.append(e(src[last:m.start()]))
        out.append(f'<a href="https://arxiv.org/abs/{e(m.group(1))}">arXiv:{e(m.group(1))}</a>')
        last = m.end()
    out.append(e(src[last:]))
    return "".join(out)


def card(p: dict, root: str, decl_href: Callable[[str], str | None]) -> str:
    st = p.get("status") or "open"
    tags = f'<span class="badge {_BADGE.get(st, "")}">{e(LIT_STATUSES.get(st, st))}</span>'
    src = ", ".join(x for x in (p.get("source"), p.get("location")) if x)
    parts = [
        f'<article class="card lit" id="{e(p["ref"])}">'
        f'<div class="card-top"><span class="ptitle"><span class="num">{e(p["ref"])}</span> '
        f'{e(p["title"])}</span><span class="badges">{tags}</span></div>',
        f'<p class="prose math pre-wrap">{e(p["statement"])}</p>',
    ]
    if src:
        title = f' — <em>{e(p["source_title"])}</em>' if p.get("source_title") else ""
        parts.append(f'<p class="small">Posed in {source_html(src)}{title}</p>')
    if p.get("rationale"):
        parts.append(
            '<details class="lit-more"><summary>What is known</summary>'
            f'<p class="prose math pre-wrap">{e(p["rationale"])}</p></details>'
        )
    if p.get("links"):
        names = []
        for l in p["links"]:
            href = decl_href(l["node"])
            name = (f'<a class="decl" href="{e(href)}">{e(l["node"])}</a>' if href
                    else f'<code>{e(l["node"])}</code>')
            names.append(f'{name} <span class="small">({e(l["role"])})</span>')
        parts.append(f'<p class="answers">In Lean: {", ".join(names)}</p>')
    parts.append("</article>")
    return "".join(parts)


def section(
    items: list[dict],
    root: str,
    *,
    domain_title: Callable[[str], str],
    topic_title: Callable[[str], str],
    decl_href: Callable[[str], str | None],
) -> str:
    """All entries, grouped by field (domain, then topic), each topic folded."""
    if not items:
        return ""
    counts = {k: sum(1 for p in items if p.get("status") == k) for k in LIT_STATUSES}
    facts = "".join(
        f'<div class="fact"><span class="k">{e(v)}</span><span class="v">{counts[k]}</span></div>'
        for k, v in LIT_STATUSES.items() if counts[k]
    )
    by_topic: dict[tuple[str, str], list[dict]] = {}
    for p in items:
        by_topic.setdefault((p.get("domain") or "", p.get("topic") or ""), []).append(p)
    order = {k: i for i, k in enumerate(LIT_STATUSES)}
    groups = []
    for (dom, top), ps in sorted(by_topic.items(),
                                 key=lambda kv: (domain_title(kv[0][0]), topic_title(kv[0][1]))):
        ps.sort(key=lambda p: (order.get(p.get("status"), 9), p["id"]))
        groups.append(
            f'<details class="lit-topic" id="lit-{e(top or "other")}">'
            f'<summary><span>{e(topic_title(top) or "Other")}</span>'
            f'<span class="small">{e(domain_title(dom))} · {len(ps)}</span></summary>'
            + "".join(card(p, root, decl_href) for p in ps)
            + "</details>"
        )
    return (
        '<section class="pgroup" id="literature"><header class="shead">'
        f'<h2>Open problems from the literature</h2><span class="n">{len(items)}</span></header>'
        '<p class="small">Questions that papers, surveys and books leave open, with where '
        "each was posed and what is known. The machine states them in Lean and works on "
        "them; an entry counts as settled only when a linked Lean theorem settles it.</p>"
        f'<div class="facts">{facts}</div>'
        + "".join(groups)
        + "</section>"
    )
