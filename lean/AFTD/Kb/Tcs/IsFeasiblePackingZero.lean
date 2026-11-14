import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasiblePacking
import AFTD.Kb.Tcs.TwoPowEqSuccIff

/-!
# is_feasible_packing_zero

Topic: combinatorics   Node: 182866ddd820

Provenance: helper lemma. folklore

The empty multiset of finite sets is a feasible packing for any parameters r, s, t, h.
-/

/-- The empty multiset is a feasible packing for any parameters. -/
theorem is_feasible_packing_zero (r s t h : ℕ) : is_feasible_packing r s t h 0 := by first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff | (simp only [is_feasible_packing] at *; first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff)
