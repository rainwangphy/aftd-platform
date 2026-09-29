#!/usr/bin/env python3
"""Pull community problems and challenges from GitHub issues into JSON.

Runs in CI before `build.py`, with the workflow's GITHUB_TOKEN; runs locally
too, without a token, against a public repository (60 requests an hour).

    python3 web/fetch_problems.py --repo rainwangphy/aftd-platform --out web/data/problems.json

The output is a build input, not a record: it is regenerated on every build
and never committed. The record is the issues themselves.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from problems import PROBLEM_LABEL, VERDICT_LABEL, normalize  # noqa: E402

API = "https://api.github.com"


def fetch(repo: str, label: str, token: str) -> list[dict]:
    out, page = [], 1
    while True:
        url = (
            f"{API}/repos/{repo}/issues?labels={label}&state=all"
            f"&per_page=100&page={page}"
        )
        req = urllib.request.Request(url)
        req.add_header("Accept", "application/vnd.github+json")
        req.add_header("X-GitHub-Api-Version", "2022-11-28")
        if token:
            req.add_header("Authorization", f"Bearer {token}")
        with urllib.request.urlopen(req, timeout=30) as r:
            batch = json.load(r)
        # The issues endpoint returns pull requests too; they are not problems.
        out += [i for i in batch if "pull_request" not in i]
        if len(batch) < 100:
            return out
        page += 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY", ""))
    ap.add_argument("--out", default=str(HERE / "data" / "problems.json"))
    args = ap.parse_args()
    if not args.repo:
        ap.error("--repo (or GITHUB_REPOSITORY) is required")
    token = os.environ.get("GITHUB_TOKEN", "")
    seen: dict[int, dict] = {}
    try:
        for label in (PROBLEM_LABEL, VERDICT_LABEL):
            for issue in fetch(args.repo, label, token):
                seen[issue["number"]] = normalize(issue)
    except urllib.error.HTTPError as err:
        # A repository that is still private, or a rate limit: build the site
        # without problems rather than not at all, and say so in the log.
        print(f"warning: could not read issues of {args.repo}: {err}", file=sys.stderr)
    items = [seen[k] for k in sorted(seen)]
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps({"repo": args.repo, "issues": items}, ensure_ascii=False, indent=1)
        + "\n",
        encoding="utf-8",
    )
    n_p = sum(1 for i in items if i["kind"] == PROBLEM_LABEL)
    print(f"wrote {out}  ({n_p} problems, {len(items) - n_p} challenges)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
