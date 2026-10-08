import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState

/-!
# RSInv

Topic: matching_markets   Node: c84116cf4142

Provenance: formalization of a published result. Source: EconCSLib, `RSInv`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**RSInv** (the deferred-acceptance rank invariant — the engine of the stability proof): for every man `j` and every woman `i` that `j` has already proposed to, `i` currently holds *some* man whom she prefers at least as much as `j`. Formally: for every `i ∈ (m.prefs j).take (s.nextChoice j)` (the prefix of `j`'s preference list `j` has cycled through), there exists `h` such that `s.holding i = some h` **and** `(w.prefs i).idxOf h ≤ (w.prefs i).idxOf j` (smaller index = higher preference). Why this is the stability lever: at termination, if `(i, j)` *were* a blocking pair — `i` and `j` mutually prefer each other to their final partners — then `j` would have proposed to `i` at some point, so `RSInv` at termination would say `i` holds someone she likes at least as much as `j`. That someone is `i`'s eventual partner (by `holding_rank_mono_run`), giving `i` no incentive to defect. Contradiction with the blocking-pair assumption. The invariant is preserved by every `daStep` (`rsinv_step`) and trivially holds at `initState` (`rsinv_init`); see also `rsinv_finalState` for the terminal form used in the stability proof.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- **RSInv** (the deferred-acceptance rank invariant — the engine of the stability proof): for every man `j` and every woman `i` that `j` has already proposed to, `i` currently holds *some* man whom she prefers at least as much as `j`. Formally: for every `i ∈ (m.prefs j).take (s.nextChoice j)` (the prefix of `j`'s preference list `j` has cycled through), there exists `h` such that `s.holding i = some h` **and** `(w.prefs i).idxOf h ≤ (w.prefs i).idxOf j` (smaller index = higher preference). Why this is the stability lever: at termination, if `(i, j)` *were* a blocking pair — `i` and `j` mutually prefer each other to their final partners — then `j` would have proposed to `i` at some point, so `RSInv` at termination would say `i` holds someone she likes at least as much as `j`. That someone is `i`'s eventual partner (by `holding_rank_mono_run`), giving `i` no incentive to defect. Contradiction with the blocking-pair assumption. The invariant is preserved by every `daStep` (`rsinv_step`) and trivially holds at `initState` (`rsinv_init`); see also `rsinv_finalState` for the terminal form used in the stability proof. -/
def RSInv (w m : Preferences n) (s : DAState n) : Prop :=
  ∀ j i : Fin n, i ∈ (m.prefs j).take (s.nextChoice j) →
    ∃ h : Fin n, s.holding i = some h ∧ (w.prefs i).idxOf h ≤ (w.prefs i).idxOf j
