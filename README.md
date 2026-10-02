# AFTD — Auto-Formalizing Theoretical Domains

**Open proof to the community. Open verdict by the community.**

AFTD is a machine that reads a curriculum of the theoretical sciences — computer
science, optimization, probability, logic, game theory, physics — states their
theorems in Lean 4, proves them against Mathlib, and publishes whatever Lean
accepts: immediately, to everyone, with no paper and no author line.

This repository is where the knowledgebase lives and where the community takes
part.

**Site:** <https://rainwangphy.github.io/aftd-platform/> ·
**Knowledgebase:** <https://rainwangphy.github.io/aftd-platform/knowledgebase/> ·
**News:** <https://rainwangphy.github.io/aftd-platform/#news> ·
**Programme:** [assets/README_AFTD.MD](assets/README_AFTD.MD)

## What is here

| Path | What it is |
|---|---|
| `lean/` | A Lean 4 project with every verified declaration, one module each under `lean/AFTD/Kb/` |
| `web/data/kb.json` | A snapshot of the knowledgebase the site is built from |
| `web/` | The site generator (Python, standard library only) |
| `web/news.json` | The announcements in the home page's News section |
| `.github/` | The forms for submitting problems and challenging results, and the workflow that publishes the site |

## Check it yourself

A declaration is here only when Lean elaborated it against Mathlib and
`#print axioms` returned nothing outside `propext`, `Classical.choice` and
`Quot.sound`. You do not have to take that on trust:

```bash
cd lean
lake exe cache get   # prebuilt Mathlib
lake build
```

## Take part

- **Submit a problem** — [open the form](https://github.com/rainwangphy/aftd-platform/issues/new?template=problem.yml).
  A maintainer reviews each submission before the machine spends anything on it.
- **Challenge a result** — [open the form](https://github.com/rainwangphy/aftd-platform/issues/new?template=verdict.yml)
  if a name claims more than its statement proves, a statement is trivial, or a
  definition is not the one the subject uses.
- **Discuss** — questions, curriculum ideas and results you built on the
  knowledgebase belong in [Discussions](https://github.com/rainwangphy/aftd-platform/discussions).

## Build the site locally

```bash
python3 web/build.py --out _site
python3 -m http.server 8765 --directory _site
```

The agents that produce the results run elsewhere; this repository receives
what they verified. Take the Lean, use it, build on it — you do not owe us a
citation.
