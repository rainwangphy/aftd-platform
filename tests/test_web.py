"""The public site: issue forms, problem status, and what gets published.

Stdlib only -- CI runs this before every deploy without installing aftd. The
things checked are the ones that fail quietly: a form label edited on GitHub
that no longer parses, a problem shown with the wrong status, a submitter's
text reaching the page unescaped, an unreviewed submission published, or a
proof announced on the News page that Lean never checked.
"""

from __future__ import annotations

import json
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "web"))

from build import build  # noqa: E402
from problems import (  # noqa: E402
    PROBLEM_FIELDS,
    VERDICT_FIELDS,
    normalize,
    parse_form,
    status,
)

FAILS = 0


def check(label: str, cond: bool, detail: str = "") -> None:
    global FAILS
    print(
        ("  PASS  " if cond else "  FAIL  ")
        + label
        + (f"   {detail}" if detail and not cond else "")
    )
    if not cond:
        FAILS += 1


def form_labels(path: Path) -> tuple[set[str], set[str]]:
    """Field labels and ids of an issue form, read without a YAML library.

    Only fields GitHub writes into the issue body as `### <label>` count, so
    markdown blocks and checkboxes are skipped.
    """
    labels, ids, kind = set(), set(), ""
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^  - type: (\w+)", line)
        if m:
            kind = m.group(1)
        m = re.match(r"^    id: (\w+)", line)
        if m and kind not in ("markdown", "checkboxes"):
            ids.add(m.group(1))
        m = re.match(r"^      label: (.+?)\s*$", line)
        if m and kind not in ("markdown", "checkboxes"):
            labels.add(m.group(1).strip('"'))
    return labels, ids


# The page every declaration lives on is the Knowledgebase -- one word -- at
# knowledgebase/. A rename that stops at the label leaves the old name in a
# URL, a breadcrumb or a form, so this looks everywhere the public reads.
KB_URL = "knowledgebase/"
OLD_NAMES = [
    (re.compile(r"knowledge[\s-]+base", re.I), 'two-word "knowledge base"'),
    # Case matters here: "how many verified results carry their name" is prose
    # about declarations; "Verified results" or a bare "Results" link is the
    # old name of the page.
    (re.compile(r"Verified results|All results|>\s*Results\s*<|Browse [^<]{0,20}results"),
     '"Results" as the name of the page'),
]
OLD_LINK = re.compile(r"""href=["'][^"']*\bresults/""")


def naming_problems(texts: dict[str, str]) -> list[str]:
    bad = []
    for where, text in texts.items():
        for rx, what in OLD_NAMES:
            m = rx.search(text)
            if m:
                bad.append(f"{where}: {what} ({m.group(0)!r})")
        if where != "results/index.html" and OLD_LINK.search(text):
            bad.append(f"{where}: links the old results/ address")
    return bad


def public_texts() -> dict[str, str]:
    """Every file in this repository a reader sees as words, not the snapshot."""
    out = {}
    for p in sorted(ROOT.rglob("*")):
        rel = p.relative_to(ROOT).as_posix()
        if (p.is_file() and p.suffix.lower() in (".md", ".yml", ".py", ".js", ".css", ".json")
                and not rel.startswith(("web/data/", "lean/", "_site/"))
                and "__pycache__" not in rel and rel != "tests/test_web.py"):
            out[rel] = p.read_text(encoding="utf-8", errors="replace")
    return out


def body(fields: dict[str, str]) -> str:
    """An issue body the way GitHub renders a submitted form."""
    return "\n\n".join(f"### {k}\n\n{v}" for k, v in fields.items())


def issue(number: int, title: str, labels: list[str], fields: dict[str, str], **kw) -> dict:
    return normalize(
        {
            "number": number,
            "title": title,
            "html_url": f"https://github.com/o/r/issues/{number}",
            "labels": [{"name": x} for x in labels],
            "user": {"login": kw.get("author", "poser")},
            "created_at": "2026-09-01T00:00:00Z",
            "state": kw.get("state", "open"),
            "state_reason": kw.get("state_reason"),
            "body": body(fields),
        }
    )


def decl(name: str, **kw) -> dict:
    d = {
        "name": name, "kind": "theorem", "is_def": False, "topic": "t1",
        "domain": "d1", "seq": 1, "informal": f"informal {name}",
        "statement": f"theorem {name} : True", "source": f"theorem {name} : True := trivial",
        "axioms": ["propext"], "clean": True, "deps": [], "used_by": [],
        "lean_path": "", "proved_at": 1788679330, "provenance": "", "citation": "",
        "reading": "", "roundtrip": "", "explanation": None, "funder": "", "problem": None,
    }
    d.update(kw)
    return d


def kb(decls: list[dict], open_nodes: list[dict]) -> dict:
    return {
        "schema": 1, "generated": "2026-09-29T00:00:00Z",
        "trusted_axioms": ["Classical.choice", "Quot.sound", "propext"],
        "totals": {
            "declarations": len(decls), "definitions": 0, "theorems": len(decls),
            "topics": 1, "domains": 1, "open": len(open_nodes), "rejected": 0,
            "spend": 1.5, "funded": 0, "currency": "USD",
            "tokens": {"input": 0, "output": 0, "cache_read": 0}, "models": [],
            "first": 0, "last": 0,
        },
        "domains": [{"name": "d1", "title": "Domain One", "description": "about d1",
                     "topics": [{"name": "t1", "title": "Topic One", "target": 10, "proved": 1}]}],
        "declarations": decls, "open": open_nodes, "grants": [],
    }


def main() -> int:
    print("issue forms")
    forms = ROOT / ".github" / "ISSUE_TEMPLATE"
    labels, ids = form_labels(forms / "problem.yml")
    check("every problem-form label is one the parser reads",
          labels == set(PROBLEM_FIELDS), f"{labels ^ set(PROBLEM_FIELDS)}")
    labels, ids = form_labels(forms / "verdict.yml")
    check("every verdict-form label is one the parser reads",
          labels == set(VERDICT_FIELDS), f"{labels ^ set(VERDICT_FIELDS)}")
    check("the verdict form has the `declaration` id the site pre-fills",
          "declaration" in ids, str(ids))

    print("parsing")
    got = parse_form(
        body({
            "Domain": "Theoretical Computer Science",
            "Topic": "_No response_",
            "Statement": "Every $n$ is\nfine.",
            "Lean statement (optional)": "```lean\ntheorem x : True := trivial\n```",
            "Before you submit": "- [X] I searched",
        }).replace("\n", "\r\n"),
        PROBLEM_FIELDS,
    )
    check("a field left empty comes back empty", got["topic"] == "", repr(got["topic"]))
    check("a multi-line field keeps its lines", got["statement"] == "Every $n$ is\nfine.",
          repr(got["statement"]))
    check("a rendered field loses its code fence",
          got["lean"] == "theorem x : True := trivial", repr(got["lean"]))
    check("a field missing from the body is empty, not absent", got["references"] == "")
    p = issue(3, "[Problem] Pumping lemma", ["problem"], {})
    check("the [Problem] prefix is dropped from the title", p["title"] == "Pumping lemma", p["title"])
    v = issue(4, "[Verdict] foo", ["verdict"], {"Declaration": "`foo`"})
    check("a verdict issue is read with the verdict form", v["kind"] == "verdict"
          and v["fields"]["declaration"] == "`foo`", str(v))

    print("status")
    acc = issue(1, "a", ["problem", "accepted"], {})
    check("unreviewed is pending", status(issue(1, "a", ["problem"], {}), []) == "pending")
    check("accepted, not formalized", status(acc, []) == "accepted")
    check("formalized, waiting", status(acc, [{"status": "stated"}]) == "formalized")
    check("stuck anywhere is needs-help",
          status(acc, [{"status": "proved"}, {"status": "stuck"}]) == "stuck")
    check("a proved declaration has no status field and counts as proved",
          status(acc, [decl("x")]) == "proved")
    check("proved only when every answer is proved",
          status(acc, [decl("x"), {"status": "stated"}]) == "formalized")
    check("declined outranks a proof",
          status(issue(1, "a", ["problem", "accepted", "declined"], {}), [decl("x")]) == "declined")
    check("closed as not planned is declined",
          status(issue(1, "a", ["problem"], {}, state="closed", state_reason="not_planned"), [])
          == "declined")

    print("build")
    evil = "<script>alert(1)</script>"
    issues = [
        issue(10, f"[Problem] Solved {evil}", ["problem", "accepted"],
              {"Domain": "Domain One", "Statement": f"Proved thing $x$ {evil}"}, author="alice"),
        issue(11, "[Problem] Secret unreviewed", ["problem"],
              {"Statement": "UNREVIEWED-TEXT-MARKER"}),
        issue(12, "[Problem] Nope", ["problem", "declined"], {"Statement": "DECLINED-BODY"}),
        issue(13, "[Problem] Stuck one", ["problem", "accepted"], {"Statement": "hard"}),
        issue(20, f"[Verdict] name {evil}", ["verdict"],
              {"Declaration": "answer_ten", "What is wrong with it?": "The name claims more"}),
    ]
    data = kb(
        [decl("answer_ten", problem=10, used_by=["plain_one"]),
         decl("plain_one", deps=["answer_ten"], informal=f"Uses answer ten {evil}")],
        [{"name": "stuck_lemma", "kind": "theorem", "status": "stuck", "topic": "t1",
          "domain": "d1", "informal": "", "statement": "theorem stuck_lemma : False",
          "attempts": 3, "deps": [], "problem": 13},
         {"name": "machine_open", "kind": "theorem", "status": "stated", "topic": "t1",
          "domain": "d1", "informal": "", "statement": "theorem machine_open : True",
          "attempts": 0, "deps": [], "problem": None},
         {"name": "loose_open", "kind": "theorem", "status": "stated", "topic": "t1",
          "domain": "d1", "informal": "", "statement": "theorem loose_open : True",
          "attempts": 0, "deps": [], "problem": None}],
    )
    data["literature"] = [
        {"id": 7, "ref": "OP-7", "title": f"Literature question {evil}",
         "statement": "Does $x$ exist?", "status": "formalized", "topic": "t1", "domain": "d1",
         "source": "arXiv:2208.08782", "source_title": "A survey", "location": "Sec. 4",
         "rationale": "LIT-WHY", "added": 0,
         "links": [{"node": "answer_ten", "role": "partial"},
                   {"node": "machine_open", "role": "statement"}]},
    ]
    cfg = {"repo": "o/r", "branch": "master", "base_url": "https://o.github.io/r/"}
    news = [
        {"date": "2026-09-30", "kind": "launch", "title": f"Old launch {evil}",
         "body": "First paragraph.\n\nSecond with `code`.",
         "links": [{"label": "Submit", "href": "submit/"},
                   {"label": "Away", "href": "https://example.org/x"}]},
        {"date": "2026-10-02", "kind": "proof", "title": "Answer ten is proved",
         "body": "NEWS-PROOF-BODY", "declarations": ["answer_ten"]},
    ] + [{"date": f"2026-09-0{d}", "kind": "launch", "title": f"Launch {d}", "body": "b"}
         for d in range(1, 5)]
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "_site"
        n = build(data, issues, cfg, out, news)
        pages = {p.relative_to(out).as_posix(): p.read_text(encoding="utf-8")
                 for p in out.rglob("*.html")}
        everything = "\n".join(pages.values())
        for rel in ("index.html", "knowledgebase/index.html", "results/index.html", "problems/index.html",
                    "submit/index.html", "404.html", "d/answer_ten/index.html",
                    "d/plain_one/index.html", "problems/10/index.html",
                    "problems/13/index.html"):
            check(f"page {rel}", rel in pages)
        print("naming")
        check("the old results/ address forwards to the knowledgebase",
              f"../{KB_URL}" in pages.get("results/index.html", ""))
        # Pages that only forward to where something moved have no layout.
        check("the old submit/ address forwards to the Problems page's guide",
              "../problems/#submit" in pages.get("submit/index.html", ""))
        prob = pages.get("problems/index.html", "")
        check("the submission guide sits at the top, with the Submit button, above the problems",
              0 <= prob.find('id="submit"') < prob.find('Submit a problem</a>')
              < prob.find("How submitting works") < prob.find("Submit one precise statement")
              < prob.find('class="facts"'))
        check("Submit is no longer a tab of its own",
              not re.search(r'<nav[^>]*>.*?>Submit<', pages["index.html"], re.S))
        moved = {"results/index.html", "news/index.html", "submit/index.html",
                 "weekly/index.html"}
        site_pages = {k: v for k, v in pages.items() if k != "404.html" and k not in moved}
        no_nav = [k for k, v in site_pages.items()
                  if not re.search(
                      rf'href="(?:\.\./)*{KB_URL}"[^>]*>Knowledgebase<', v)]
        check("every page's navigation links the Knowledgebase by name", not no_nav, str(no_nav[:5]))
        bad = naming_problems(pages) + naming_problems(public_texts())
        check("nothing public still calls it Results or the knowledge base, or links results/",
              not bad, "\n        " + "\n        ".join(bad[:20]))
        check("submitted text never reaches a page unescaped", evil not in everything)
        check("an unreviewed submission is counted, not published",
              "UNREVIEWED-TEXT-MARKER" not in everything and "problems/11/index.html" not in pages)
        check("a declined problem gets no page of its own",
              "problems/12/index.html" not in pages and "DECLINED-BODY" not in everything)
        check("the pending count links to GitHub", "awaiting review" in pages["problems/index.html"])
        print("chat")
        chat = pages.get("chat/index.html", "")
        check("the chat page is built and in the navigation",
              "static/chat.js" in chat and 'href="../chat/" aria-current="page">Ask<' in chat)
        index_raw = (out / "chat" / "kb-index.json").read_text(encoding="utf-8")
        detail = json.loads((out / "chat" / "kb-detail.json").read_text(encoding="utf-8"))
        by = {x["name"]: x for x in json.loads(index_raw)["entries"]}
        check("the chat index holds every declaration, unproved statement and problem",
              {"answer_ten", "plain_one", "machine_open", "OP-7", "#10"} <= set(by), str(sorted(by)))
        check("the chat index keeps statuses exact",
              by["answer_ten"]["status"] == "verified in Lean"
              and by["machine_open"]["status"].startswith("stated")
              and by["#10"]["lean"] == [{"name": "answer_ten", "role": "answer"}])
        check("the chat index links entries relative to the site root",
              by["answer_ten"]["url"] == "d/answer_ten/" and by["OP-7"]["url"] == "problems/#OP-7")
        check("an unreviewed or declined submission never reaches the chat index",
              "#11" not in by and "#12" not in by and "UNREVIEWED-TEXT-MARKER" not in index_raw
              and "DECLINED-BODY" not in index_raw)
        check("the chat detail holds each declaration's Lean source",
              set(detail) == {"answer_ten", "plain_one"} and "source" in detail["answer_ten"])
        prob = pages.get("problems/10/index.html", "")
        check("a problem page links the declaration that answers it",
              'href="../../d/answer_ten/"' in prob)
        check("a problem page credits who posed it", "@alice" in prob)
        check("a problem with every answer proved shows as proved", "st-proved" in prob)
        check("a problem whose lemma is stuck shows as needs help",
              "st-stuck" in pages.get("problems/13/index.html", ""))
        dp = pages.get("d/answer_ten/index.html", "")
        check("a declaration page links back to its problem", 'href="../../problems/10/"' in dp)
        check("a challenge is shown on the declaration it names", "issues/20" in dp)
        check("used-by is linked", 'href="../../d/plain_one/"' in dp)
        check("the challenge button pre-fills the declaration",
              "template=verdict.yml" in dp and "declaration=answer_ten" in dp)
        check("an open machine statement is listed as open",
              "machine_open" in pages["problems/index.html"])
        kbpage = pages["knowledgebase/index.html"]
        check("an unproved statement is listed in the knowledgebase, marked unproved",
              "machine_open" in kbpage and "not yet proved" in kbpage
              and 'href="../d/machine_open/"' not in kbpage)
        machine = pages["problems/index.html"].split('id="unproved"', 1)[-1]
        check("an unproved statement of no problem is listed on its own",
              "loose_open" in machine)
        check("... but a statement of a problem only on that problem's card",
              "machine_open" not in machine and "stuck_lemma" not in machine)
        probs = pages["problems/index.html"]
        lit = probs.split('id="formalized"', 1)[-1].split("</section>", 1)[0]
        check("an open problem from the list sits under its status, like a community one",
              "OP-7" in lit and "LIT-WHY" in lit and 'id="literature"' not in probs)
        check("a listed problem links its arXiv source",
              'href="https://arxiv.org/abs/2208.08782"' in lit)
        check("a listed problem links a verified declaration, and names an unproved one unlinked",
              'href="../d/answer_ten/"' in lit and "<code>machine_open</code>" in lit)
        check("the counts returned match",
              n == {"declarations": 2, "problems": 2, "news": 6, "weekly": 0, "monthly": 0}, str(n))

        print("news")
        home = pages["index.html"]
        news = home.split('id="news"', 1)[-1].split("</section>", 1)[0]
        check("the home page has a News section", 'id="news"' in home)
        check("News is a section of the home page, not a tab",
              not any(">News<" in m for v in pages.values()
                      for m in re.findall(r'<nav aria-label="Site">(.*?)</nav>', v, re.S)))
        check("news is newest first", 0 < news.find("Answer ten is proved") < news.find("Old launch"))
        check("a proof announcement links the declaration", 'href="d/answer_ten/"' in news)
        check("paragraphs and code are kept",
              "<p class=\"prose\">Second with <code>code</code>.</p>" in news)
        check("a site link is relative to the root, an outside one left alone",
              'href="submit/"' in news and 'href="https://example.org/x"' in news)
        check("an entry can be linked to", 'id="n-2026-10-02-answer-ten-is-proved"' in news)
        older = news.split('class="news-older"', 1)
        check("only the latest entries are open; the rest are folded away",
              len(older) == 2 and "Earlier news (2)" in older[1]
              and "Launch 2" in older[1] and "Launch 2" not in older[0])
        check("the footer links the News section on every page",
              all('index.html#news">News<' in v for v in site_pages.values()))
        check("the old news/ address forwards to the section, keeping an entry's anchor",
              "location.hash || \"#news\"" in pages.get("news/index.html", ""))
        check("there is no feed", not (out / "news" / "feed.xml").exists()
              and "atom" not in everything.lower())

        print("graph")
        gp = pages.get("knowledgebase/index.html", "")
        m = re.search(r'<script type="application/json" id="g-data">(.*?)</script>', gp, re.S)
        check("the graph page carries its data", m is not None)
        g = json.loads(m.group(1)) if m else {"nodes": [], "edges": []}
        names = [x[0] for x in g["nodes"]]
        check("every declaration is a node", sorted(names) == ["answer_ten", "plain_one"], str(names))
        check("a use is an edge from the user to what it uses",
              g["edges"] == [[names.index("plain_one"), names.index("answer_ten")]] if len(names) == 2 else False,
              str(g["edges"]))
        check("the graph's data cannot close its script element early",
              "</script" not in m.group(1).lower() if m else False)
        check("the graph opens the knowledgebase page, above the list",
              0 < gp.find('id="graph"') < gp.find('id="kb"'))
        check("the graph is part of the knowledgebase, not a tab of its own",
              "graph/index.html" not in pages
              and not any("graph" in m.lower() for v in pages.values()
                          for m in re.findall(r'<nav aria-label="Site">(.*?)</nav>', v, re.S)))
        check("a declaration page opens the graph on itself",
              'href="../../knowledgebase/?n=answer_ten#graph"' in pages.get("d/answer_ten/index.html", ""))
        check("the graph script ships with the site", (out / "static" / "graph.js").is_file())

    print("weekly")
    card = {"headline": "Ten is the answer", "outcome": "proved",
            "question": "WEEKLY-QUESTION", "answer": "WEEKLY-ANSWER", "why": "WEEKLY-WHY",
            "idea": "", "source": "arXiv:2609.10493", "main": "answer_ten",
            "declarations": ["answer_ten", "plain_one"], "highlight": True}
    report = {
        "week": "2026-W40", "start": "2026-09-28", "end": "2026-10-04", "partial": False,
        "format": 2, "title": f"Ten is the answer {evil}", "summary": "WEEKLY-SUMMARY",
        "fields": [{"name": "Domain One", "context": "WEEKLY-CONTEXT", "results": [card]}],
        "outlook": ["WEEKLY-OUTLOOK"], "glossary": [{"term": "EF1", "meaning": "WEEKLY-TERM"}],
        "numbers": "Lean accepted 1 new theorem this week.", "minutes": 3,
        "disclaimer": "Written by a model.",
        "outcomes": {"proved": "Proved", "disproved": "Disproved", "partial": "Partial",
                     "new": "New result"},
    }
    older = {**report, "week": "2026-W39", "start": "2026-09-21", "end": "2026-09-27",
             "title": "An earlier week"}
    wnews = [{"date": "2026-10-05", "kind": "weekly", "week": "2026-W40",
              "title": "Week of 28 Sep - 4 Oct 2026: ten", "body": "WEEKLY-LEDE",
              "links": [{"label": "Read the weekly report", "href": "weekly/2026-W40/"}]}]
    month = {**report, "week": "2026-09", "start": "2026-09-01", "end": "2026-09-30",
             "period": "month", "title": "MONTHLY-TITLE", "summary": "MONTHLY-SUMMARY"}
    mnews = [{"date": "2026-10-01", "kind": "monthly", "month": "2026-09",
              "title": "September 2026: ten", "body": "MONTHLY-LEDE",
              "links": [{"label": "Read the monthly report", "href": "monthly/2026-09/"}]}]
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "_site"
        n = build(data, [], cfg, out, wnews + mnews, [older, report], [month])
        pages = {p.relative_to(out).as_posix(): p.read_text(encoding="utf-8")
                 for p in out.rglob("*.html")}
        wk = pages.get("weekly/2026-W40/index.html", "")
        idx = pages.get("reports/index.html", "")
        check("each report has a page, and there is an index", wk != "" and idx != ""
              and "weekly/2026-W39/index.html" in pages)
        check("the counts include the reports", n.get("weekly") == 2, str(n))
        check("the index is newest first",
              0 < idx.find("2026-W40/") < idx.find("2026-W39/"))
        check("a result links its main theorem and its paper",
              'href="../../d/answer_ten/"' in wk and "arxiv.org/abs/2609.10493" in wk)
        check("supporting theorems are folded under the card",
              "1 supporting theorem<" in wk and 'href="../../d/plain_one/"' in wk)
        check("the week in one minute comes first, with its highlights",
              0 < wk.find("WEEKLY-SUMMARY") < wk.find("At a glance") < wk.find("WEEKLY-QUESTION")
              and 'href="#r1">Ten is the answer<' in wk)
        check("every result is in the at-a-glance table, with its outcome",
              'class="wk-field"' in wk and ">Domain One</th>" in wk and "wk-proved" in wk)
        check("a card has the question, the answer and why it matters",
              all(x in wk for x in ("WEEKLY-ANSWER", "WEEKLY-WHY", "The question")))
        check("context, outlook, terms, numbers and reading time are kept",
              all(x in wk for x in ("WEEKLY-CONTEXT", "WEEKLY-OUTLOOK", "WEEKLY-TERM",
                                    "Lean accepted 1 new theorem", "3 min read")))
        check("a report's text is escaped", evil not in wk and evil not in idx)
        check("a report links the week before it",
              'href="../../weekly/2026-W39/"' in wk and "Earlier week" in wk)
        check("the weekly News item links to its report",
              'href="weekly/2026-W40/"' in pages["index.html"] and "Weekly report" in pages["index.html"])
        check("every page's navigation links the summary reports",
              all(re.search(r'href="(?:\.\./)*reports/"[^>]*>Summary Report<', v)
                  for k, v in pages.items() if k not in {"404.html", "results/index.html",
                                                          "news/index.html", "submit/index.html",
                                                          "weekly/index.html"}))
        check("the old address of the reports forwards to them",
              "reports/" in pages.get("weekly/index.html", "") and "Moved" in pages["weekly/index.html"])
        mo = pages.get("monthly/2026-09/index.html", "")
        check("a monthly report has its page, laid out like a week's",
              "Monthly report" in mo and "The month in one minute" in mo
              and "MONTHLY-SUMMARY" in mo and "September 2026" in mo
              and 'href="../../d/answer_ten/"' in mo)
        check("the counts include the monthly reports", n.get("monthly") == 1, str(n))
        check("the index lists every report in one list, each tagged by its period",
              idx.count('class="news-item rp"') == 3 and "badge rp-week" in idx
              and "badge rp-month" in idx and 'href="../monthly/2026-09/"' in idx
              and "<h2>Weekly Reports</h2>" not in idx)
        check("the index is newest first across periods",
              0 < idx.find("weekly/2026-W40/") < idx.find("monthly/2026-09/") < idx.find("weekly/2026-W39/"))
        check("the index has a search box, a period filter and a month filter",
              'id="rq"' in idx and 'data-period="week"' in idx and 'data-period="month"' in idx
              and '<option value="2026-09">September 2026</option>' in idx
              and '<option value="2026-10">October 2026</option>' in idx and "app.js" in idx)
        check("a week that straddles two months is under both",
              'data-period="week" data-months="2026-09 2026-10"' in idx)
        check("a monthly News item links to its report",
              'href="monthly/2026-09/"' in pages["index.html"] and "Monthly report" in pages["index.html"])

    def wrefused(reports: list[dict], news: list[dict] | None = None) -> str:
        try:
            with tempfile.TemporaryDirectory() as tmp:
                build(data, [], cfg, Path(tmp) / "_site", news or [], reports)
        except ValueError as ex:
            return str(ex)
        return ""

    check("a well-formed report builds", wrefused([report]) == "")
    def with_card(**kw) -> dict:
        return {**report, "fields": [{**report["fields"][0], "results": [{**card, **kw}]}]}

    check("a report may not name an open statement as verified",
          "machine_open" in wrefused([with_card(declarations=["answer_ten", "machine_open"])]))
    check("a result's main theorem must be among its declarations",
          wrefused([with_card(main="plain_one", declarations=["answer_ten"])]) != "")
    check("an unknown outcome is refused", wrefused([with_card(outcome="maybe")]) != "")
    with tempfile.TemporaryDirectory() as tmp:
        build(data, [], cfg, Path(tmp) / "_site", [], [with_card(outcome="formalized")])
        fz = (Path(tmp) / "_site" / "weekly" / "2026-W40" / "index.html").read_text()
    check("a formalization says what is checked, not what we showed",
          "What is checked" in fz and "What we showed" not in fz and "wk-formalized" in fz)
    check("a report in an older format is refused, not half-rendered",
          "format" in wrefused([{**report, "format": 1}]))
    check("a malformed week is refused", wrefused([{**report, "week": "2026-40"}]) != "")
    check("a weekly News item needs its report", "2026-W40" in wrefused([], wnews))

    def mrefused(reports: list[dict], news: list[dict] | None = None) -> str:
        try:
            with tempfile.TemporaryDirectory() as tmp:
                build(data, [], cfg, Path(tmp) / "_site", news or [], [], reports)
        except ValueError as ex:
            return str(ex)
        return ""

    check("a well-formed monthly report builds", mrefused([month]) == "")
    check("a monthly report needs a YYYY-MM label", mrefused([{**month, "week": "2026-W39"}]) != "")
    check("a weekly report is not filed as a monthly one",
          "not a monthly" in mrefused([{**month, "period": "week"}]))
    check("a monthly News item needs its report", "2026-09" in mrefused([], mnews))

    def refused(entry: dict) -> str:
        try:
            with tempfile.TemporaryDirectory() as tmp:
                build(data, [], cfg, Path(tmp) / "_site", [entry])
        except ValueError as ex:
            return str(ex)
        return ""

    base = {"date": "2026-10-02", "kind": "proof", "title": "t", "body": "b"}
    check("a proof announcement must name what it proves", refused(base) != "")
    check("a proof announcement may not name an open statement",
          "machine_open" in refused({**base, "declarations": ["machine_open"]}))
    check("a proof announcement may not name something unknown",
          "nope" in refused({**base, "declarations": ["nope"]}))
    check("an unknown kind is refused", refused({**base, "kind": "rumour"}) != "")
    daily = {**base, "kind": "daily"}
    check("a daily entry may prove nothing", refused(daily) == "")
    check("a daily entry may not list an open statement as proved",
          "machine_open" in refused({**daily, "declarations": ["machine_open"]}))
    check("a malformed date is refused", refused({**base, "kind": "launch", "date": "2 Oct"}) != "")

    snap = ROOT / "web" / "data" / "kb.json"
    if snap.is_file():
        print("committed snapshot")
        real = json.loads(snap.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "_site"
            news_file = ROOT / "web" / "news.json"
            news = json.loads(news_file.read_text())["entries"] if news_file.is_file() else []
            weekly = [json.loads(f.read_text(encoding="utf-8"))
                      for f in sorted((ROOT / "web" / "weekly").glob("*.json"))]
            try:
                n = build(real, [], json.loads((ROOT / "web" / "site.json").read_text()), out,
                          news, weekly)
                err = ""
            except ValueError as ex:
                n, err = {"declarations": -1}, str(ex)
            check("the committed news names only what the snapshot verified", not err, err)
            check("the committed snapshot builds", n["declarations"] == len(real["declarations"]))
            missing = [d["name"] for d in real["declarations"]
                       for dep in d["deps"] if dep not in {x["name"] for x in real["declarations"]}]
            check("every dependency of a verified declaration is itself on the site",
                  not missing, str(missing[:5]))

    print(f"\n{'ALL PASSED' if not FAILS else str(FAILS) + ' FAILED'}")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
