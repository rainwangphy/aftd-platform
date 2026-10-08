import AFTD.Prelude

/-!
# BayesianMechanism

Topic: mechanism_design   Node: 9679669fec25

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A mechanism in an incomplete-information environment. `T i` is agent `i`'s true type space, `M i` is agent `i`'s message space, and `prior` is the common prior over type profiles. This keeps the Harsanyi-style uncertainty separate from the mechanism map itself: the mechanism acts on reported messages, while the prior lives as extra Bayesian structure.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A mechanism in an incomplete-information environment. `T i` is agent `i`'s true type space, `M i` is agent `i`'s message space, and `prior` is the common prior over type profiles. This keeps the Harsanyi-style uncertainty separate from the mechanism map itself: the mechanism acts on reported messages, while the prior lives as extra Bayesian structure. -/
structure BayesianMechanism
    (I : Type*) (T : I → Type*) [∀ i, MeasurableSpace (T i)]
    (M : I → Type*) (O : Type*) where
  /-- Common prior probability measure over true type profiles. -/
  prior : MeasureTheory.Measure (∀ i, T i)
  /-- The prior is a probability measure. -/
  prob_prior : MeasureTheory.IsProbabilityMeasure prior
  /-- Outcome rule as a function of reported messages. -/
  outcome : (∀ i, M i) → O

-- Intentionally global so measure-theoretic lemmas can infer the probability
-- structure from a mechanism term without repeated local `haveI := B.prob_prior`.

attribute [instance] BayesianMechanism.prob_prior
