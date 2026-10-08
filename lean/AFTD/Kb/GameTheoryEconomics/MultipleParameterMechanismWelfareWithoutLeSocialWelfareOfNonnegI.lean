import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfareEqValueAddWelfareWithout

/-!
# MultipleParameterMechanism.welfareWithout_le_socialWelfare_of_nonneg_i

Topic: mechanism_design   Node: 5063e5f5fe15

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.welfareWithout_le_socialWelfare_of_nonneg_i`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If agent `i`'s valuation is nonnegative, then the welfare of agents other than `i` is bounded by total social welfare.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
omit [Fintype A] [Nonempty A] in
/-- If agent `i`'s valuation is nonnegative, then the welfare of agents other than `i` is bounded by total social welfare. -/
lemma MultipleParameterMechanism.welfareWithout_le_socialWelfare_of_nonneg_i
    (v : ∀ _ : I, Valuation A ℝ)
    (i : I) (hi_nonneg : ∀ a : A, 0 ≤ v i a) (a : A) :
    welfareWithout v i a ≤ socialWelfare v a := by
  have hdecomp := socialWelfare_eq_value_add_welfareWithout v i a
  have hi := hi_nonneg a
  linarith
