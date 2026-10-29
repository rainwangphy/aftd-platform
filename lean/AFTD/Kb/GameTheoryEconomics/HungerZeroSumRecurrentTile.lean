import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerIter

/-!
# hunger_zero_sum_recurrent_tile

Topic: combinatorial_games   Node: dc6458420036

Provenance: formalization of a published result. Source: arXiv:2610.08949, Section 3

For an n-by-n real matrix P, the zero-sum recurrent hunger tile is the set of vectors h in R^n with zero coordinate sum such that hunger_iter P n h = h under the hunger dynamics.
-/

/-- The recurrent hunger tile in the zero-sum hyperplane, consisting of zero-sum vectors fixed under n iterations of the hunger map. -/
def hunger_zero_sum_recurrent_tile {n : ℕ} [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) := {h : Fin n → ℝ | ∑ i, h i = 0 ∧ hunger_iter P n h = h}
