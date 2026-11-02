import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionDominatedCandidates
import AFTD.Kb.GameTheoryEconomics.RegularizedPluralityWeight

/-!
# in_regularized_plurality_veto_core_empty_coalition

Topic: social_choice   Node: d210529787e9

Provenance: helper lemma. arXiv:2610.26535

For any election profile, candidate a, and regularization strength ε, the empty set of voters satisfies the condition that its proportion is at most the sum of regularized plurality weights of candidates it dominates.
-/

/-- The empty voter coalition satisfies the core condition for any regularization strength. -/
lemma in_regularized_plurality_veto_core_empty_coalition {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C] (prof : V → LinearOrder C) (ε : ℝ) (a : C) : ((∅ : Finset V).card : ℝ) / (Fintype.card V : ℝ) ≤ ∑ c ∈ coalition_dominated_candidates prof a (∅ : Finset V), regularized_plurality_weight prof ε c := by
  simp [coalition_dominated_candidates]
