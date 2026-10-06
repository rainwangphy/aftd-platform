"""Community problems and challenges: read from GitHub issues, placed on the site.

Two issue forms feed the site (`.github/ISSUE_TEMPLATE/`):

* `problem.yml` -- someone submits a statement for the machine to attempt.
* `verdict.yml` -- someone challenges a verified declaration: the name says
  more than the statement, the statement is trivial, the definition is not the
  one the subject uses. Correctness is not up for challenge; everything else is.

GitHub renders a submitted form as Markdown, one `### <label>` heading per
field, so that is what is parsed back here. The labels below must match the
forms word for word; `tests/test_web.py` holds them to it.

Nothing a submitter wrote is trusted. It is escaped wherever it is shown, it
never reaches a shell, and a Lean statement in a submission is reference text
for the Proposer -- it is never elaborated as-is, because Lean runs code at
elaboration time (`#eval`, `run_cmd`, `initialize`).

Stdlib only: this runs in CI, where the aftd package and its dependencies are
not installed.
"""

from __future__ import annotations

import re

PROBLEM_LABEL = "problem"
VERDICT_LABEL = "verdict"
ACCEPTED_LABEL = "accepted"
DECLINED_LABELS = frozenset({"declined", "duplicate", "invalid", "wontfix"})

PROBLEM_FIELDS = {
    "Domain": "domain",
    "Topic": "topic",
    "Statement": "statement",
    "What kind of statement is this?": "kind",
    "References": "references",
    "Lean statement (optional)": "lean",
    "Anything else": "context",
}
VERDICT_FIELDS = {
    "Declaration": "declaration",
    "What is wrong with it?": "reason",
    "Explanation": "explanation",
}

# The order statuses are shown in, with the words the site uses for them.
STATUSES = {
    "proved": "Proved",
    "stuck": "Needs help",
    "formalized": "In progress",
    "accepted": "Open",
    "pending": "Awaiting review",
    "declined": "Declined",
}

_HEADING = re.compile(r"^###\s+(.+?)\s*$", re.M)
_FENCE = re.compile(r"\A```[\w-]*\n(.*?)\n?```\Z", re.S)
_NO_RESPONSE = "_No response_"
_TITLE_PREFIX = re.compile(r"^\s*\[(problem|verdict)\]\s*:?\s*", re.I)


def parse_form(body: str, fields: dict[str, str]) -> dict[str, str]:
    """An issue-form body back into {key: value}; unknown headings are ignored.

    A field left empty comes back from GitHub as `_No response_`, and a field
    with `render:` set comes back wrapped in a code fence; both are undone.
    """
    out = {key: "" for key in fields.values()}
    body = (body or "").replace("\r\n", "\n")
    heads = list(_HEADING.finditer(body))
    for i, m in enumerate(heads):
        key = fields.get(m.group(1))
        if key is None:
            continue
        end = heads[i + 1].start() if i + 1 < len(heads) else len(body)
        value = body[m.end() : end].strip()
        if value == _NO_RESPONSE:
            value = ""
        fence = _FENCE.match(value)
        if fence:
            value = fence.group(1).strip()
        out[key] = value
    return out


def normalize(issue: dict) -> dict:
    """The parts of a GitHub API issue the site uses, and nothing else."""
    labels = sorted(
        (lb.get("name") if isinstance(lb, dict) else str(lb)) or ""
        for lb in issue.get("labels") or []
    )
    kind = VERDICT_LABEL if VERDICT_LABEL in labels else PROBLEM_LABEL
    fields = PROBLEM_FIELDS if kind == PROBLEM_LABEL else VERDICT_FIELDS
    return {
        "number": int(issue["number"]),
        "kind": kind,
        "title": _TITLE_PREFIX.sub("", issue.get("title") or "").strip(),
        "url": issue.get("html_url") or "",
        "state": issue.get("state") or "open",
        "state_reason": issue.get("state_reason") or "",
        "labels": labels,
        "author": ((issue.get("user") or {}).get("login")) or "",
        "created_at": issue.get("created_at") or "",
        "closed_at": issue.get("closed_at") or "",
        "comments": int(issue.get("comments") or 0),
        "fields": parse_form(issue.get("body") or "", fields),
    }


def status(problem: dict, nodes: list[dict]) -> str:
    """Where a problem stands, from its labels and the nodes that answer it.

    `nodes` are the knowledgebase nodes whose `problem` is this issue. The
    machine's record outranks the labels -- a proved answer is proved even if
    nobody got round to closing the issue -- except that a declined problem
    stays declined.
    """
    labels = set(problem.get("labels") or [])
    if labels & DECLINED_LABELS or problem.get("state_reason") == "not_planned":
        return "declined"
    if nodes:
        if all(n.get("status", "proved") == "proved" for n in nodes):
            return "proved"
        if any(n.get("status") == "stuck" for n in nodes):
            return "stuck"
        return "formalized"
    if ACCEPTED_LABEL in labels:
        return "accepted"
    return "pending"
