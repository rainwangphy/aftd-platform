# AFTD: An Open Programme for Auto-formalizing Theoretical Domains

**Open proof to the community. Open verdict by the community.**

Prove the theoretical results, and open source them to everyone.

AFTD is a machine that reads a curriculum of theoretical subjects, states
theorems in Lean 4, proves them against Mathlib, and adds whatever survives to
a public knowledgebase. It runs unattended. Nothing enters the knowledgebase
because a language model said it was true.

---

## The idea

Theory is written to be read by people, and it is checked by people. That
checking is the bottleneck: it does not scale, it is unevenly distributed
across subjects, and most of it never gets written down in a form another
machine or another person can reuse.

Lean 4 and Mathlib remove the bottleneck for the *checking* half. A proof
either elaborates or it does not, and the answer costs seconds, not a referee
year. What has been missing is the other half: someone to decide what is worth
stating, to write the statement, to attempt the proof, and to keep doing it for
a subject at a time rather than for one paper.

That half is now cheap enough to automate. So the programme is simple:

> Point a loop at a curriculum of theoretical domains. Let it state and prove,
> forever. Keep only what Lean accepts. Publish all of it, immediately, to
> everyone.

The unit of progress is not a paper. It is one Lean declaration that a machine
can check, that other declarations can build on, and that anyone can `import`
tomorrow without asking permission or citing us.

## What "proved" counts as here

This is the only part of the programme worth being strict about, so it is
strict in a way that is mechanical rather than editorial.

A declaration is in the knowledgebase only when:

1. **Lean 4 elaborates it against Mathlib**, with zero errors.
2. **`#print axioms` returns nothing outside `propext`, `Classical.choice` and
   `Quot.sound`.** That single check rules out `sorry` (which shows up as
   `sorryAx`), `native_decide` (`Lean.ofReduceBool`), and any axiom an agent
   quietly declared for itself. A model's claim to have proved something is not
   evidence; this is.
3. **It survives a two-way round trip.** One model reads only the Lean — never
   the English — and writes down what the statement actually asserts; another
   model reads only the English and re-formalizes it blind. Lean itself is
   asked first whether the two signatures imply each other. If the Lean and
   the English disagree, the statement goes back for revision. This is what
   stops a technically valid theorem that says something other than what it
   claims to say.
4. **Its name is not a claim it cannot back.** A theorem named after `NP` whose
   `NP` is a universally quantified predicate is rejected before any model is
   asked for an opinion — the name is an assertion about the content, and the
   round trip is blind to it.
5. **It did not reinvent a concept Mathlib already has.** A new definition must
   cite the literature or prove that the agent searched Mathlib and the
   knowledgebase first. A privately restated `NP` severs everything downstream
   from every real theorem about `NP`, silently.

Everything in the knowledgebase rebuilds offline from source with
`lake build`. The verification story does not depend on our database, our
scheduler, or our word.

## How the machine is put together

Three agents work around one dependency graph of theorems. The scheduler that
drives them is **not** a language model — what to work on, when to give up and
when to split a hard theorem into lemmas are all decided by deterministic rules
over the graph. The models supply judgement (what is worth stating, how to
prove it, how to decompose it); they never supply control flow. That division
is the reason the thing can run for days without drifting.

- **Proposer** — works inside one topic at a time. Transcribes known results
  from the literature, and proposes its own: generalizations, converses,
  bridges between topics. Every statement must type-check and pass the round
  trip before it is even queued.
- **Prover** — proves exactly one node at a time, seeing only the goal, the
  *signatures* of its direct dependencies, and retrieved Mathlib lemmas. When
  it cannot finish, it does not fake it and does not silently prove something
  weaker: it files the lemmas it needs, already type-checked, and the graph
  grows a rung.
- **Manager** — owns the graph. Reviews new statements, rejects the duplicate,
  the trivial and the vacuous, keeps the graph acyclic, and steers coverage
  toward whichever topic is furthest behind its target.

A bounded context per node is what keeps the cost flat: the knowledgebase can
grow from ten declarations to a thousand without the prompts growing with it.

## Where it stands

As of 20 September 2026, from a standing start:

| | |
|---|---|
| Machine-verified declarations | **115** — 82 theorems, 33 definitions |
| Topics with results | 18, across 3 domains |
| Curriculum | 6 domains, 49 topics, 1,035 declarations targeted |
| Rejected by the Manager | 4 |
| Stated, not yet proved | 14 |
| API spend to date | about **$21** |

The curriculum covers theoretical computer science (24 topics), optimization,
probability and statistics, logic and foundations, game theory and economics,
and theoretical physics. Three of those six have been opened so far; the rest
are waiting on compute, not on code.

Roughly nineteen cents per verified declaration, at the current mix of easy
transcription and modest original results, using inexpensive models. That
number will go up as the frontier gets harder, and it is an average over
everything the run spent — including the attempts that failed. It is not a
price list.

## What you get

Everything, as it is produced, with no gate and no embargo:

- **Lean sources** under `lean/AFTD/Kb/`, one module per declaration,
  rebuildable with `lake build`.
- **A Markdown knowledgebase** — every declaration with its informal
  statement, its Lean source and its dependencies.
- **A results board** — a single HTML page of everything verified, grouped by
  domain and topic, searchable, each declaration one click from its full proof
  and its `#print axioms` verdict.
- **A dependency graph** you can click through, from a theorem down to the
  lemmas it stands on.

## No paper, and no credit to the team

We are not going to write a paper about this, and no one on this side gets an
author line.

That is a deliberate choice, not modesty. The moment the output exists to
support a publication, the incentives bend: toward results that look novel
rather than results that are useful, toward holding work back until it can be
announced, toward a claim of authorship over mathematics that a machine checked
and that mostly already belonged to the people who first proved it. A knowledgebase that anyone can `import` is worth more than a paper that cites it.

So: take the Lean, use it, build on it, teach from it. You do not owe us a
citation.

The second half of that — **open verdict by the community** — is about the
judgements Lean does not make. Whether a proof is correct is mechanical, public
and not up for discussion: it elaborates and `#print axioms` comes back clean,
or it is not here. Every other verdict is open. Whether a statement was worth
making, whether its name is honest about what it asserts, whether a definition
is the one the subject actually uses, whether a topic's target is the right
shape — none of that is settled by two anonymous referees behind a journal. The
Manager's triage is a first pass, not a last word; the graph page shows what
was rejected alongside what was kept; and disagreeing with either is an issue
on the repository, in public, against a knowledgebase you can rebuild yourself.

## Funding, and the board

The only real cost is tokens.

If you fund the research by providing the tokens, you will be acknowledged on
the board — the same page that shows the results — and the acknowledgement is
specific rather than decorative. Every API call the run makes is charged, in
time order, to the oldest grant that had arrived and still had money in it. A
declaration carries whoever paid for the work in the window that ended when
Lean accepted it: the proposing, the failed attempts and the verification
included, not just the successful proof. Each funder's entry says how much they
gave, how much of it has actually been spent, and how many verified results
carry their name.

Two things that should be said plainly. Money buys attempts, not results —
a grant that funds a stretch where everything got stuck still gets its entry,
because it paid for the same machinery. And a name on the board is an
acknowledgement of support, not authorship of the mathematics; funders do not
direct what gets proved, though the curriculum has room and a stated interest
in a domain is welcome.

To fund it, or to donate API credits, open an issue at
[github.com/rainwangphy/aftd-platform](https://github.com/rainwangphy/aftd-platform).

We thank you for the support.

## Ways to help that are not money

- **Compute.** API credits are tokens; tokens are the whole cost.
- **Lean and Mathlib expertise.** The fastest way to help is to look at what
  the Prover got stuck on and say which Mathlib lemma it was missing.
- **Curriculum.** Tell us which topics are missing, and which canonical
  references a topic should be formalizing from.
- **Reading the statements.** The round trip catches a lot; it does not catch
  everything. A theorem that is valid but says less than its name suggests is
  the failure mode worth reporting.

## What this is not

It is not an attempt on open problems. It is not a claim that mathematicians
are replaceable. Most of what is in the knowledgebase is known mathematics,
carefully transcribed and machine-checked, plus a growing minority of modest
original statements — generalizations, converses, bridges — that the Manager
judged worth keeping. The value is in the aggregate and in the fact that it is
verified, open and cumulative, not in any single line of it.

