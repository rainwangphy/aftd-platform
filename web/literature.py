"""Open problems from the knowledgebase's open-problem list, as Problems-page cards.

Every entry is a question a paper, survey or book leaves open, kept in the
knowledgebase's open-problem list and exported by `scripts/snapshot.py` as
`literature` in `data/kb.json`. The Problems page lists them together with the
community's problems, under the same statuses (`STATUS_OF`). An entry counts
as proved only when a linked Lean theorem settles it (`settled_in_lean`,
derived by the snapshot from the proved declarations).

Stdlib only, like the rest of `web/`.
"""

from __future__ import annotations

import html
import re
from typing import Callable

e = html.escape

# The list's statuses, as the Problems page's (see problems.STATUSES).
STATUS_OF = {
    "settled_in_lean": "proved",
    "formalized": "formalized",
    "open": "accepted",
    "reported_solved": "accepted",
}
_ARXIV = re.compile(r"arXiv:\s*(\d{4}\.\d{4,5})", re.I)


def status(p: dict) -> str:
    return STATUS_OF.get(p.get("status") or "open", "accepted")


def source_html(src: str) -> str:
    """The source as text, with every arXiv id linked to its abstract page."""
    out, last = [], 0
    for m in _ARXIV.finditer(src):
        out.append(e(src[last:m.start()]))
        out.append(f'<a href="https://arxiv.org/abs/{e(m.group(1))}">arXiv:{e(m.group(1))}</a>')
        last = m.end()
    out.append(e(src[last:]))
    return "".join(out)


def card(p: dict, badges: str, decl_href: Callable[[str], str | None]) -> str:
    """One entry; `badges` is the status and topic, rendered by the caller."""
    src = ", ".join(x for x in (p.get("source"), p.get("location")) if x)
    parts = [
        f'<article class="card problem lit" id="{e(p["ref"])}">'
        f'<div class="card-top"><span class="ptitle"><span class="num">{e(p["ref"])}</span> '
        f'{e(p["title"])}</span><span class="badges">{badges}</span></div>',
        f'<p class="prose math pre-wrap">{e(p["statement"])}</p>',
    ]
    if src:
        title = f' — <em>{e(p["source_title"])}</em>' if p.get("source_title") else ""
        parts.append(f'<p class="small">Posed in {source_html(src)}{title}</p>')
    if p.get("status") == "reported_solved":
        parts.append('<p class="small">Reported solved in the literature; not yet checked in Lean.</p>')
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
