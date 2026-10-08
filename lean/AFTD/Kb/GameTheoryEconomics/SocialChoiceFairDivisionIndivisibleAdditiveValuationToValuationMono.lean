import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation

/-!
# SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_mono

Topic: fair_division   Node: da4aa9f072e3

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_mono`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Additive valuations with nonnegative weights are monotone: sub-bundles have no greater value than their supersets.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
/-- Additive valuations with nonnegative weights are monotone: sub-bundles have no greater value than their supersets. -/
lemma SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation_mono [DecidableEq G]
    (w : AdditiveValuation N G)
    (hnn : ∀ (i : N) (g : G), 0 ≤ w.weight i g)
    (i : N) {S T : Finset G} (h : T ⊆ S) :
    w.toValuation.val i T ≤ w.toValuation.val i S := by
  simp only [toValuation]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => hnn i x)
