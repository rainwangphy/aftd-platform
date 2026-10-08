import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGTransferMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValueOfAllocation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismEfficientAllocation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismMaxWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithoutUpdateSelf
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfareEqValueAddWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVcgPayment

/-!
# MultipleParameterMechanism.VCGMechanism_quasiLinearUtility_eq_socialWelfare_sub_maxWelfareWithout

Topic: mechanism_design   Node: 55b298dd0743

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.VCGMechanism_quasiLinearUtility_eq_socialWelfare_sub_maxWelfareWithout`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VCG utility can be rewritten as total welfare under the profile that uses agent `i`'s true valuation and keeps all other reports fixed, minus the maximal welfare achievable by the other agents alone.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MultipleParameterMechanism in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- VCG utility can be rewritten as total welfare under the profile that uses agent `i`'s true valuation and keeps all other reports fixed, minus the maximal welfare achievable by the other agents alone. -/
lemma MultipleParameterMechanism.VCGMechanism_quasiLinearUtility_eq_socialWelfare_sub_maxWelfareWithout
    (reports trueTypes : ∀ _ : I, Valuation A ℝ) (i : I) :
    MechanismWithTransfers.quasiLinearUtility
        VCGTransferMechanism valueOfAllocation id id reports trueTypes i =
      socialWelfare (Function.update reports i (trueTypes i)) (efficientAllocation reports) -
        maxWelfareWithout reports i := by
  let aStar := efficientAllocation reports
  have hdecomp :
      socialWelfare (Function.update reports i (trueTypes i)) aStar =
        trueTypes i aStar + welfareWithout reports i aStar := by
    simpa [Function.update, welfareWithout_update_self reports i (trueTypes i) aStar] using
      socialWelfare_eq_value_add_welfareWithout
        (Function.update reports i (trueTypes i)) i aStar
  simp [MechanismWithTransfers.quasiLinearUtility, valueOfAllocation,
    VCGTransferMechanism, VCGMechanism, vcgPayment]
  dsimp [aStar] at hdecomp
  linarith
