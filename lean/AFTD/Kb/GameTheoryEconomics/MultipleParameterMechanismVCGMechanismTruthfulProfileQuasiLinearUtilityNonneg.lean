import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGTransferMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValueOfAllocation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGMechanismTruthfulQuasiLinearUtilityNonneg
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# MultipleParameterMechanism.VCGMechanism_truthful_profile_quasiLinearUtility_nonneg

Topic: mechanism_design   Node: 8d9c28a098ad

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.VCGMechanism_truthful_profile_quasiLinearUtility_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The same nonnegative-utility result for the fully truthful report profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MultipleParameterMechanism in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- The same nonnegative-utility result for the fully truthful report profile. -/
theorem MultipleParameterMechanism.VCGMechanism_truthful_profile_quasiLinearUtility_nonneg
    (v : ∀ _ : I, Valuation A ℝ)
    (hnonneg : ∀ i : I, ∀ a : A, 0 ≤ v i a)
    (i : I) :
    0 ≤ MechanismWithTransfers.quasiLinearUtility
      VCGTransferMechanism valueOfAllocation id id v v i := by
  simpa [Function.update_eq_self] using
    VCGMechanism_truthful_quasiLinearUtility_nonneg (v := v) hnonneg i v
