import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimEnvelopeFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
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
# BayesianSingleItemAuction.equilibriumPayoff_eq_of_hasInterimEnvelopeFormula_of_interimAllocProb_eq

Topic: mechanism_design   Node: 285a9520f7e9

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.equilibriumPayoff_eq_of_hasInterimEnvelopeFormula_of_interimAllocProb_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Same `q_i` and zero-type payment give the same truthful payoff.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Same `q_i` and zero-type payment give the same truthful payoff. -/
theorem BayesianSingleItemAuction.equilibriumPayoff_eq_of_hasInterimEnvelopeFormula_of_interimAllocProb_eq
    (A B : BayesianSingleItemAuction I)
    (henvA : A.HasInterimEnvelopeFormula) (henvB : B.HasInterimEnvelopeFormula)
    (i : I)
    (hQ : ∀ z : ℝ, A.interimAllocProb i z = B.interimAllocProb i z)
    (hM0 : A.interimExpectedPayment i 0 = B.interimExpectedPayment i 0)
    (v_i : ℝ) :
    A.equilibriumPayoff i v_i = B.equilibriumPayoff i v_i := by
  have hW0 : A.equilibriumPayoff i 0 = B.equilibriumPayoff i 0 := by
    rw [equilibriumPayoff, interimQuasiLinearUtility,
      equilibriumPayoff, interimQuasiLinearUtility, hM0]
    ring
  have hQfun : (fun z => A.interimAllocProb i z) = fun z => B.interimAllocProb i z :=
    funext hQ
  calc
    A.equilibriumPayoff i v_i
        = A.equilibriumPayoff i 0 + ∫ z in 0..v_i, A.interimAllocProb i z :=
          henvA i v_i
    _ = B.equilibriumPayoff i 0 + ∫ z in 0..v_i, B.interimAllocProb i z := by
          rw [hW0, hQfun]
    _ = B.equilibriumPayoff i v_i := (henvB i v_i).symm
