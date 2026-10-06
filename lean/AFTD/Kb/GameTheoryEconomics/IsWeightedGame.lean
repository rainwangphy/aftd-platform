import AFTD.Prelude

/-!
# is_weighted_game

Topic: general_equilibrium   Node: 3d9ce6ecd565

Provenance: formalization of a published result. Source: What Semivalues Cannot See: The Information Content of Anonymous Marginal Values, arXiv:2607.07013, Sec. 10 (simple game, weighted game as in the monograph Simple Games: Desirability Relations, Trading, Pseudoweightings (1999), swing table)

A game is weighted if there are nonnegative player weights w and a quota q such that a coalition wins exactly when its total weight is at least q.
-/

/-- A game is weighted (Taylor-Zwicker): there are nonnegative weights `w` and a quota `q` such that a coalition wins exactly when its total weight reaches the quota. -/
def is_weighted_game {n : ℕ} (v : Finset (Fin n) → Bool) : Prop :=
  ∃ (w : Fin n → ℝ) (q : ℝ), (∀ i, 0 ≤ w i) ∧ ∀ S, v S = true ↔ q ≤ ∑ i ∈ S, w i
