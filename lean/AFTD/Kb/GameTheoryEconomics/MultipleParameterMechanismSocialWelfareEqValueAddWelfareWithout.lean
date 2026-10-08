import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout

/-!
# MultipleParameterMechanism.socialWelfare_eq_value_add_welfareWithout

Topic: mechanism_design   Node: 970feb885dd7

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.socialWelfare_eq_value_add_welfareWithout`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Social welfare decomposes into agent `i`'s value plus the welfare of the other agents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
omit [Fintype A] [Nonempty A] in
/-- Social welfare decomposes into agent `i`'s value plus the welfare of the other agents. -/
lemma MultipleParameterMechanism.socialWelfare_eq_value_add_welfareWithout
    (v : ∀ _ : I, Valuation A ℝ) (i : I) (a : A) :
    socialWelfare v a = v i a + welfareWithout v i a := by
  rw [socialWelfare, welfareWithout]
  exact (Finset.add_sum_erase Finset.univ (fun j => v j a) (Finset.mem_univ i)).symm
