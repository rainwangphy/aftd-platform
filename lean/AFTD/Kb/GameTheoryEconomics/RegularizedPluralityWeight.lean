import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PluralityVotes

/-!
# regularized_plurality_weight

Topic: social_choice   Node: f44679df4023

Provenance: formalization of a published result. Source: arXiv:2610.26535, Definition 4(1)

For finite voter type V, finite candidate type C, a profile prof : V → LinearOrder C, regularization strength ε : ℝ, and candidate c : C, regularized_plurality_weight prof ε c is ((plurality_votes prof c : ℝ) / (Fintype.card V : ℝ) + ε) / (1 + (Fintype.card C : ℝ) * ε).
-/

/-- The regularized plurality weight of candidate c with regularization strength epsilon. -/
noncomputable def regularized_plurality_weight {V C : Type*} [Fintype V] [Fintype C]
    (prof : V → LinearOrder C) (ε : ℝ) (c : C) : ℝ :=
  ((plurality_votes prof c : ℝ) / (Fintype.card V : ℝ) + ε) / (1 + (Fintype.card C : ℝ) * ε)
