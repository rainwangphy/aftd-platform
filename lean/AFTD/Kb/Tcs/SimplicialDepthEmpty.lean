import AFTD.Prelude
import AFTD.Kb.Tcs.SimplicialDepth
import AFTD.Kb.Tcs.TwoPowEqSuccIff

/-!
# simplicial_depth_empty

Topic: combinatorics   Node: 4a9e93e62f8e

Provenance: helper lemma. folklore

For every point p in the Euclidean plane, the simplicial depth of p with respect to the empty set of points is 0.
-/

/-- Sanity lemma: the simplicial depth of any point with respect to the empty set is 0. -/
theorem simplicial_depth_empty (p : ℝ × ℝ) : simplicial_depth p ∅ = 0 := by first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff | (simp only [simplicial_depth] at *; first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff)
