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
import xml.etree.ElementTree as ET
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
         decl("plain_one", deps=["answer_ten"])],
        [{"name": "stuck_lemma", "kind": "theorem", "status": "stuck", "topic": "t1",
          "domain": "d1", "informal": "", "statement": "theorem stuck_lemma : False",
          "attempts": 3, "deps": [], "problem": 13},
         {"name": "machine_open", "kind": "theorem", "status": "stated", "topic": "t1",
          "domain": "d1", "informal": "", "statement": "theorem machine_open : True",
          "attempts": 0, "deps": [], "problem": None}],
    )
    cfg = {"repo": "o/r", "branch": "master", "base_url": "https://o.github.io/r/"}
    news = [
        {"date": "2026-09-30", "kind": "launch", "title": f"Old launch {evil}",
         "body": "First paragraph.\n\nSecond with `code`.",
         "links": [{"label": "Submit", "href": "submit/"},
                   {"label": "Away", "href": "https://example.org/x"}]},
        {"date": "2026-10-02", "kind": "proof", "title": "Answer ten is proved",
         "body": "NEWS-PROOF-BODY", "declarations": ["answer_ten"]},
    ]
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "_site"
        n = build(data, issues, cfg, out, news)
        pages = {p.relative_to(out).as_posix(): p.read_text(encoding="utf-8")
                 for p in out.rglob("*.html")}
        feed = (out / "news" / "feed.xml").read_text(encoding="utf-8")
        everything = "\n".join(pages.values())
        for rel in ("index.html", "knowledgebase/index.html", "results/index.html", "problems/index.html",
                    "submit/index.html", "404.html", "d/answer_ten/index.html",
                    "d/plain_one/index.html", "problems/10/index.html",
                    "problems/13/index.html", "news/index.html"):
            check(f"page {rel}", rel in pages)
        print("naming")
        check("the old results/ address forwards to the knowledgebase",
              f"../{KB_URL}" in pages.get("results/index.html", ""))
        site_pages = {k: v for k, v in pages.items() if k != "404.html"}
        no_nav = [k for k, v in site_pages.items()
                  if k != "results/index.html" and not re.search(
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
        machine = pages["problems/index.html"].split('id="open"', 1)[-1]
        check("a stuck lemma of a problem is not listed again as machine-posed",
              "machine_open" in machine and "stuck_lemma" not in machine)
        check("the counts returned match",
              n == {"declarations": 2, "problems": 2, "news": 2}, str(n))

        print("news")
        news_page = pages.get("news/index.html", "")
        check("news is newest first", 0 < news_page.find("Answer ten is proved") < news_page.find("Old launch"))
        check("a proof announcement links the declaration", 'href="../d/answer_ten/"' in news_page)
        check("paragraphs and code are kept", "<p class=\"prose\">Second with <code>code</code>.</p>" in news_page)
        check("a site link is relative to the root, an outside one left alone",
              'href="../submit/"' in news_page and 'href="https://example.org/x"' in news_page)
        check("every page links News in its navigation",
              all(re.search(r'href="(?:\.\./)*news/"[^>]*>News<', v)
                  for k, v in site_pages.items() if k != "results/index.html"))
        check("the home page shows the latest news",
              'href="news/#n-2026-10-02-answer-ten-is-proved"' in pages["index.html"])
        try:
            root = ET.fromstring(feed)
        except ET.ParseError as ex:
            root = None
            check("the feed is well-formed XML", False, str(ex))
        ns = {"a": "http://www.w3.org/2005/Atom"}
        entries = root.findall("a:entry", ns) if root is not None else []
        check("the feed has every entry, newest first",
              [x.findtext("a:title", namespaces=ns) for x in entries][:1] == ["Answer ten is proved"]
              and len(entries) == 2)
        check("feed links are absolute",
              "https://o.github.io/r/d/answer_ten/" in feed and 'href="../' not in feed)
        check("pages point feed readers at the feed", 'application/atom+xml' in pages["index.html"])

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
    check("a malformed date is refused", refused({**base, "kind": "launch", "date": "2 Oct"}) != "")

    snap = ROOT / "web" / "data" / "kb.json"
    if snap.is_file():
        print("committed snapshot")
        real = json.loads(snap.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "_site"
            news_file = ROOT / "web" / "news.json"
            news = json.loads(news_file.read_text())["entries"] if news_file.is_file() else []
            try:
                n = build(real, [], json.loads((ROOT / "web" / "site.json").read_text()), out, news)
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
