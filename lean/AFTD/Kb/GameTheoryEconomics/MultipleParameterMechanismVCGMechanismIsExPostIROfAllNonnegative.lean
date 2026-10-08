import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersIsQuasiLinearExPostIR
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGTransferMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValueOfAllocation
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVcgPayment
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismEfficientAllocation
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGMechanismTruthfulQuasiLinearUtilityNonneg
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersIsExPostIR

/-!
# MultipleParameterMechanism.VCGMechanism_isExPostIR_of_all_nonnegative

Topic: mechanism_design   Node: b322430a3616

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.VCGMechanism_isExPostIR_of_all_nonnegative`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VCG satisfies the `MechanismWithTransfers.isExPostIR` predicate under the ambient assumption that every valuation in the unrestricted type space is nonnegative. For concrete domains, this assumption is usually enforced by choosing a nonnegative valuation subtype.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MultipleParameterMechanism in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- VCG satisfies the `MechanismWithTransfers.isExPostIR` predicate under the ambient assumption that every valuation in the unrestricted type space is nonnegative. For concrete domains, this assumption is usually enforced by choosing a nonnegative valuation subtype. -/
theorem MultipleParameterMechanism.VCGMechanism_isExPostIR_of_all_nonnegative
    (hnonneg :
      ∀ v : (∀ _ : I, Valuation A ℝ), ∀ i : I, ∀ a : A, 0 ≤ v i a) :
    MechanismWithTransfers.isQuasiLinearExPostIR
      (M := (VCGTransferMechanism :
        MechanismWithTransfers I (fun _ => Valuation A ℝ) A ℝ))
      valueOfAllocation id id := by
  intro trueTypes i r
  simpa [MechanismWithTransfers.quasiLinearUtility, MechanismWithTransfers.isQuasiLinearExPostIR,
    valueOfAllocation, VCGTransferMechanism, VCGMechanism] using
    VCGMechanism_truthful_quasiLinearUtility_nonneg
      (v := trueTypes) (hnonneg trueTypes) i r
