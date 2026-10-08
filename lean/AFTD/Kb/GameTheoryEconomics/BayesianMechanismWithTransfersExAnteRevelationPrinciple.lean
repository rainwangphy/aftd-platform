import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersIsExAnteBayesianNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersExAnteRevelationPrincipleConclusion
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismIsMeasurableStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersExAnteExpectedUtility
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDeviate
import AFTD.Kb.GameTheoryEconomics.DirectBayesianMechanismWithTransfersTruthfulStrategy
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelation
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismStrategy
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedPayments
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismInducedMessages
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelationAllocationTruthful
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelationPaymentsTruthful
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# BayesianMechanismWithTransfers.exAnte_revelation_principle

Topic: mechanism_design   Node: df6d98fe7a0e

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.exAnte_revelation_principle`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Revelation principle, ex-ante form: if `σ` is a Bayesian Nash equilibrium of the indirect mechanism, then truthful reporting is a Bayesian Nash equilibrium of the induced direct mechanism. This is the ex-ante version because `IsExAnteBayesianNashEquilibrium` above is defined via ex-ante expected utility rather than interim conditional utility. References: * [Myerson 1979, "Incentive Compatibility and the Bargaining Problem"] * [Krishna 2010, Ch. 5]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
omit [∀ i, MeasurableSpace (T i)] in
/-- Revelation principle, ex-ante form: if `σ` is a Bayesian Nash equilibrium of the indirect mechanism, then truthful reporting is a Bayesian Nash equilibrium of the induced direct mechanism. This is the ex-ante version because `IsExAnteBayesianNashEquilibrium` above is defined via ex-ante expected utility rather than interim conditional utility. References: * [Myerson 1979, "Incentive Compatibility and the Bargaining Problem"] * [Krishna 2010, Ch. 5] -/
theorem BayesianMechanismWithTransfers.exAnte_revelation_principle
    [DecidableEq I]
    [∀ i, MeasurableSpace (T i)]
    [∀ i, MeasurableSpace (M i)]
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M)
    (hσ : B.IsExAnteBayesianNashEquilibrium u σ) :
    B.ExAnteRevelationPrincipleConclusion u σ := by
  rcases hσ with ⟨hσ_meas, hσ_eq⟩
  constructor
  · intro i
    rw [DirectBayesianMechanismWithTransfers.truthfulStrategy]
    apply measurable_id
  · intro i report hreport
    specialize hσ_eq i (fun t => σ i (report t)) ((hσ_meas i).comp hreport)
    rw [(by
        unfold BayesianMechanismWithTransfers.exAnteExpectedUtility
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        simp only [BayesianMechanismWithTransfers.inducedAllocation,
          BayesianMechanismWithTransfers.inducedPayments]
        apply congrArg₂ (fun a p => u (B.allocationRule a) (B.paymentRule p) t i)
        all_goals
          ext j
          by_cases h : j = i
          · subst h
            simp [BayesianMechanism.inducedMessages, BayesianMechanismWithTransfers.deviate]
          · simp [BayesianMechanism.inducedMessages, BayesianMechanismWithTransfers.deviate,
              DirectBayesianMechanismWithTransfers.truthfulStrategy, h] :
        (B.directRevelation σ).exAnteExpectedUtility u
            (deviate DirectBayesianMechanismWithTransfers.truthfulStrategy i report) i =
          B.exAnteExpectedUtility u (deviate σ i (fun t => σ i (report t))) i),
      (by
        unfold BayesianMechanismWithTransfers.exAnteExpectedUtility
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        rfl :
        (B.directRevelation σ).exAnteExpectedUtility u
            DirectBayesianMechanismWithTransfers.truthfulStrategy i =
          B.exAnteExpectedUtility u σ i)]
    assumption
