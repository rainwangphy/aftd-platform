import AFTD.Prelude
import AFTD.Kb.Tcs.TwistedFrobeniusMap

/-!
# twisted_frobenius_map_one

Topic: combinatorics   Node: 8d6dda61ef43

Provenance: helper lemma. scout/2611-17378-a-19-5-lower-bound-for-the-four-dimensional-erd-h-o-s-box-p.md:118

For any field $K$ and parameter $q$, the twisted Frobenius map sends $1$ to $1$.
-/

/-- Sanity check: the twisted Frobenius map sends 1 to 1. -/
theorem twisted_frobenius_map_one (q : ℕ) {K : Type*} [Field K] :
    twisted_frobenius_map q (1 : K) = 1 := by
  simp [twisted_frobenius_map]
