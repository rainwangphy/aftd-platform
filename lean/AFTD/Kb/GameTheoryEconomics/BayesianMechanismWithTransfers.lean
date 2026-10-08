import AFTD.Prelude

/-!
# BayesianMechanismWithTransfers

Topic: mechanism_design   Node: 33d62c096c4d

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A transfer mechanism in an incomplete-information environment. As in `MechanismWithTransfers`, the allocation and payment rules are stored separately, while the common prior records the incomplete-information structure. Utility is intentionally left external.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A transfer mechanism in an incomplete-information environment. As in `MechanismWithTransfers`, the allocation and payment rules are stored separately, while the common prior records the incomplete-information structure. Utility is intentionally left external. -/
structure BayesianMechanismWithTransfers
    (I : Type*) (T : I → Type*) [∀ i, MeasurableSpace (T i)]
    (M : I → Type*) (A : Type*) (P : Type*) where
  /-- Common prior probability measure over true type profiles. -/
  prior : MeasureTheory.Measure (∀ i, T i)
  /-- The prior is a probability measure. -/
  prob_prior : MeasureTheory.IsProbabilityMeasure prior
  /-- Allocation rule from reported messages. -/
  allocationRule : (∀ i, M i) → A
  /-- Payment rule from reported messages. -/
  paymentRule : (∀ i, M i) → I → P

-- Intentionally global so transfer-mechanism terms expose their probability
-- structure directly to measure-theoretic typeclass search.

attribute [instance] BayesianMechanismWithTransfers.prob_prior
