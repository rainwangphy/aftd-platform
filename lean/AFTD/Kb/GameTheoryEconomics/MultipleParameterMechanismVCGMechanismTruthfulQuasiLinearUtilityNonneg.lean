import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGTransferMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValueOfAllocation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismEfficientAllocation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismMaxWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithoutLeSocialWelfareOfNonnegI
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismEfficientAllocationIsOptimal
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfareEqValueAddWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVcgPayment
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# MultipleParameterMechanism.VCGMechanism_truthful_quasiLinearUtility_nonneg

Topic: mechanism_design   Node: 2236751d9e0e

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.VCGMechanism_truthful_quasiLinearUtility_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If agent `i` reports truthfully in the VCG mechanism, then their quasi-linear utility is nonnegative against arbitrary reports by the other agents, assuming `i`'s true valuation is nonnegative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MultipleParameterMechanism in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- If agent `i` reports truthfully in the VCG mechanism, then their quasi-linear utility is nonnegative against arbitrary reports by the other agents, assuming `i`'s true valuation is nonnegative. -/
theorem MultipleParameterMechanism.VCGMechanism_truthful_quasiLinearUtility_nonneg
    (v : ∀ _ : I, Valuation A ℝ)
    (hnonneg : ∀ i : I, ∀ a : A, 0 ≤ v i a)
    (i : I) (r : ∀ _ : I, Valuation A ℝ) :
    0 ≤ MechanismWithTransfers.quasiLinearUtility
      VCGTransferMechanism valueOfAllocation id id (Function.update r i (v i)) v i := by
  let reports := Function.update r i (v i)
  let aStar := efficientAllocation reports
  have hi_nonneg : ∀ a : A, 0 ≤ reports i a := by
    intro a
    simp [reports, hnonneg i a]
  have hmax_le :
      maxWelfareWithout reports i ≤ socialWelfare reports aStar := by
    rw [maxWelfareWithout]
    exact Finset.sup'_le Finset.univ_nonempty (welfareWithout reports i)
      (fun a _ =>
        le_trans (welfareWithout_le_socialWelfare_of_nonneg_i reports i hi_nonneg a)
          (efficientAllocation_isOptimal reports a))
  have hdecomp :
      socialWelfare reports aStar = reports i aStar + welfareWithout reports i aStar :=
    socialWelfare_eq_value_add_welfareWithout reports i aStar
  have hreport_i : reports i aStar = v i aStar := by
    simp [reports]
  simp [MechanismWithTransfers.quasiLinearUtility, valueOfAllocation,
    VCGTransferMechanism, VCGMechanism, vcgPayment]
  dsimp [reports, aStar] at hmax_le hdecomp hreport_i
  linarith
