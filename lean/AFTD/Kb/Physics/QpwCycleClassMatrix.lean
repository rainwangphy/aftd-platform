import AFTD.Prelude

/-!
# qpwCycleClassMatrix

Topic: statistical_mechanics   Node: df2dc8f4fcb7

Provenance: helper lemma. step towards quantum_permutation_walk_slow_mode_chebyshev_semicircle_limit

The normalized class-average matrix of the m-cycle conjugacy class in S_n, acting on ℂ^{S_n} by the left-regular action: entry (g,h) is 1/#(m-cycles) when g·h⁻¹ has cycle type {m} and 0 otherwise. (Mathlib's cycleType omits fixed points, so cycleType = {m} means "exactly one nontrivial cycle, of length m", i.e. g·h⁻¹ is an m-cycle with all other points fixed; such permutations exist exactly when m ≤ n.)
-/

/-- Class-average matrix of the m-cycle class of S_n in the left regular representation. -/
noncomputable def qpwCycleClassMatrix (n m : ℕ) : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ := fun g h ↦ if (g * h⁻¹).cycleType = {m} then
      ((({c : Equiv.Perm (Fin n) | c.cycleType = {m}} : Finset (Equiv.Perm (Fin n))).card : ℂ)⁻¹)
    else 0
