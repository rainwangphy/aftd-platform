import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimEnvelopeFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasNonnegativeInterimAllocationIntegralOnSupport
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIndividuallyRationalOnSupport
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
import AFTD.Kb.GameTheoryEconomics.TypeCDF
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplyFst
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplySnd
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivSymmApply
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedSellerRevenueInEnvironmentSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.isIndividuallyRationalOnSupport_iff_interimExpectedPayment_zero_nonpos

Topic: mechanism_design   Node: 0f8a419e22fd

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.isIndividuallyRationalOnSupport_iff_interimExpectedPayment_zero_nonpos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

[MSZ 12.52] Supportwise IR iff zero-type payment is nonpositive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- [MSZ 12.52] Supportwise IR iff zero-type payment is nonpositive. -/
theorem BayesianSingleItemAuction.isIndividuallyRationalOnSupport_iff_interimExpectedPayment_zero_nonpos
    (A : BayesianSingleItemAuction I)
    (henv : A.HasInterimEnvelopeFormula)
    (hint_nonneg : A.HasNonnegativeInterimAllocationIntegralOnSupport) :
    A.IsIndividuallyRationalOnSupport ↔
      ∀ i : I, A.interimExpectedPayment i 0 ≤ 0 := by
  constructor
  · intro hIR i
    have hW0 : 0 ≤ A.equilibriumPayoff i 0 :=
      hIR i 0 le_rfl (A.typeData.cdf i).omega_nonneg
    rw [equilibriumPayoff, interimQuasiLinearUtility] at hW0
    linarith
  · intro hM0 i v_i hv_nonneg hv_le
    have hW0 : 0 ≤ A.equilibriumPayoff i 0 := by
      rw [equilibriumPayoff, interimQuasiLinearUtility]
      have hM := hM0 i
      linarith
    have hint : 0 ≤ ∫ z in 0..v_i, A.interimAllocProb i z :=
      hint_nonneg i v_i hv_nonneg hv_le
    have hsum : 0 ≤ A.equilibriumPayoff i 0 +
        ∫ z in 0..v_i, A.interimAllocProb i z :=
      add_nonneg hW0 hint
    simpa [henv i v_i] using hsum
