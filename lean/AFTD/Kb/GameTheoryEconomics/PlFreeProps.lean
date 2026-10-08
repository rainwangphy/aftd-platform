import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget

/-!
# pl_free_props

Topic: matching_markets   Node: 34305d6c99e0

Provenance: formalization of a published result. Source: EconCSLib, `pl_free_props`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Helper: membership in the proposerList implies freedom and proposal target.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- Helper: membership in the proposerList implies freedom and proposal target. -/
lemma pl_free_props {n : ℕ} (s : DAState n) (m : Preferences n) (j k : Fin n) :
    let pl : Fin n → List (Fin n) := fun j' =>
      (Finset.univ.filter (fun i =>
        isFree s i && (propTarget m i (s.nextChoice i) == some j'))).val.toList
    k ∈ pl j →
    isFree s k = true ∧ propTarget m k (s.nextChoice k) = some j := by
  intro pl hk
  change k ∈ (Finset.univ.filter (fun i =>
    isFree s i && (propTarget m i (s.nextChoice i) == some j))).val.toList at hk
  simp only [Multiset.mem_toList, Finset.mem_val, Finset.mem_filter,
    Finset.mem_univ, true_and, Bool.and_eq_true, beq_iff_eq] at hk
  exact hk
