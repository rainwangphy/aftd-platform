import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelation
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedAllocation

/-!
# BayesianMechanismWithTransfers.directRevelation_allocation_truthful

Topic: mechanism_design   Node: 3f84c5268ffb

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.directRevelation_allocation_truthful`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Under truthful reporting in the induced direct mechanism, the realized allocation agrees definitionally with the original mechanism played under `σ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- Under truthful reporting in the induced direct mechanism, the realized allocation agrees definitionally with the original mechanism played under `σ`. -/
@[simp] lemma BayesianMechanismWithTransfers.directRevelation_allocation_truthful
    (B : BayesianMechanismWithTransfers I T M A P)
    (σ : StrategyProfile T M) (t : ∀ i, T i) :
    (B.directRevelation σ).allocationRule t = B.inducedAllocation σ t :=
  rfl
