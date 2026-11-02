import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionDominatedCandidates
import AFTD.Kb.GameTheoryEconomics.RegularizedPluralityWeight

/-!
# in_regularized_plurality_veto_core

Topic: social_choice   Node: 6ab7e3565ab4

Provenance: formalization of a published result. Source: arXiv:2610.26535, Definition 4 and Lemma 1

A candidate a is in the regularized plurality veto core at regularization strength ε if for every subset S of voters, the fraction |S|/|V| is at most the sum over candidates c in coalition_dominated_candidates prof a S of regularized_plurality_weight prof ε c.
-/

/-- Membership of candidate a in the regularized plurality veto core at regularization strength ε. -/
def in_regularized_plurality_veto_core {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C] (prof : V → LinearOrder C) (ε : ℝ) (a : C) : Prop := ∀ S : Finset V, (S.card : ℝ) / (Fintype.card V : ℝ) ≤ ∑ c ∈ coalition_dominated_candidates prof a S, regularized_plurality_weight prof ε c
