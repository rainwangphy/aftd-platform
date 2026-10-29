import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerZeroSumRecurrentTile
import AFTD.Kb.GameTheoryEconomics.HungerIter

/-!
# hunger_zero_sum_recurrent_tile_subset_zero_sum

Topic: combinatorial_games   Node: c4255a4173b9

Provenance: helper lemma. arXiv:2610.08949, Section 3

The zero-sum recurrent hunger tile is contained in the zero-sum hyperplane.
-/

/-- Every element of the zero-sum recurrent hunger tile has zero coordinate sum. -/
theorem hunger_zero_sum_recurrent_tile_subset_zero_sum {n : ℕ} [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℝ) :
    hunger_zero_sum_recurrent_tile P ⊆ {h : Fin n → ℝ | ∑ i, h i = 0} := fun _h hh => hh.1
