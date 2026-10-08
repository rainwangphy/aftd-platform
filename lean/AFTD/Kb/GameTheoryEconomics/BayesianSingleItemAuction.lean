import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# BayesianSingleItemAuction

Topic: mechanism_design   Node: d5706b615f27

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A direct Bayesian single-item auction with scalar private types and probabilistic allocation. The allocation rule returns a function `Q : I → ℝ`, where `Q i` is agent `i`'s probability of receiving the item under the reported type profile. This matches the allocation/payment shape of `SingleParameterMechanism I ℝ`. The mechanism is direct: the message space equals the type space, which is taken to be `ℝ` for each agent, and payments are real-valued. Continuous-type data are stored separately in `typeData`, while the Bayesian prior is recorded by extra fields.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
/-- A direct Bayesian single-item auction with scalar private types and probabilistic allocation. The allocation rule returns a function `Q : I → ℝ`, where `Q i` is agent `i`'s probability of receiving the item under the reported type profile. This matches the allocation/payment shape of `SingleParameterMechanism I ℝ`. The mechanism is direct: the message space equals the type space, which is taken to be `ℝ` for each agent, and payments are real-valued. Continuous-type data are stored separately in `typeData`, while the Bayesian prior is recorded by extra fields. -/
structure BayesianSingleItemAuction (I : Type*)
    extends SingleParameterMechanism I ℝ where
  /-- Common prior probability measure over true type profiles. -/
  prior : MeasureTheory.Measure (∀ _ : I, ℝ)
  /-- The prior is a probability measure. -/
  prob_prior : MeasureTheory.IsProbabilityMeasure prior
  /-- Opponent-type prior `μᵢ` used for interim expectations conditional on a
  fixed report by agent `i`. -/
  opponentPrior : (i : I) → MeasureTheory.Measure (OpponentTypeProfile I i)
  /-- Each opponent-type prior is a probability measure. -/
  prob_opponentPrior :
    ∀ i : I, MeasureTheory.IsProbabilityMeasure (opponentPrior i)
  /-- Continuous private-value support and CDF data for each agent. -/
  typeData : ContinuousTypeProfile I

-- Intentionally global so integration lemmas can recover the auction prior
-- from the auction term without repeated local instance setup.

attribute [instance] BayesianSingleItemAuction.prob_prior
