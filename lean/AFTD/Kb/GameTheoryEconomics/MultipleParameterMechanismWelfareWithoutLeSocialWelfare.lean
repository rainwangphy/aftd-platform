import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare

/-!
# MultipleParameterMechanism.welfareWithout_le_socialWelfare

Topic: mechanism_design   Node: b08c08c7b12e

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.welfareWithout_le_socialWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If all valuations are nonnegative, then the welfare of agents other than `i` is bounded by total social welfare.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
omit [Fintype A] [Nonempty A] in
/-- If all valuations are nonnegative, then the welfare of agents other than `i` is bounded by total social welfare. -/
lemma MultipleParameterMechanism.welfareWithout_le_socialWelfare
    (v : ∀ _ : I, Valuation A ℝ)
    (hnonneg : ∀ i : I, ∀ a : A, 0 ≤ v i a)
    (i : I) (a : A) :
    welfareWithout v i a ≤ socialWelfare v a := by
  rw [socialWelfare, welfareWithout]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.erase_subset i Finset.univ)
    (fun j _ _ => hnonneg j a)
