import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsIrreducibleRealMatrix

/-!
# is_irreducible_real_matrix_uniform

Topic: combinatorial_games   Node: 50cbf5352589

Provenance: helper lemma. folklore

For any positive natural number n, an n-by-n real matrix P whose entries all equal 1/n is irreducible.
-/

/-- The uniform transition matrix with all entries 1/n is irreducible. -/
theorem is_irreducible_real_matrix_uniform (n : ℕ) [NeZero n] (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, P i j = 1 / (n : ℝ)) : is_irreducible_real_matrix P := by
  intro i j
  use 1
  rw [pow_one, hP]
  exact one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos n))
