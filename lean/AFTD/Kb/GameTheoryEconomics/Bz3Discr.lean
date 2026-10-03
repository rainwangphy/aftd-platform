import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Bz3Cnt

/-!
# bz3_discr

Topic: general_equilibrium   Node: 79503d148b19

Rational discrepancy for the target (3/10, 7/10, 0) of the index given by the pivot counts of a winning pattern.
-/

/-- The rational discrepancy for target `(3/10, 7/10, 0)` of the index with pivot counts `bz3_cnt x`. -/
def bz3_discr (x : Fin 8 → Bool) : ℚ :=
  let T : ℚ := (bz3_cnt x 0 + bz3_cnt x 1 + bz3_cnt x 2 : ℕ)
  |3 / 10 - (bz3_cnt x 0 : ℚ) / T| + |7 / 10 - (bz3_cnt x 1 : ℚ) / T| + |0 - (bz3_cnt x 2 : ℚ) / T|
