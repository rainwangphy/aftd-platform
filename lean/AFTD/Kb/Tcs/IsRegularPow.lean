import AFTD.Prelude
import AFTD.Kb.Tcs.IsRegularMul
import AFTD.Kb.Tcs.IsRegularOne

/-!
# is_regular_pow

Topic: automata   Node: 9974dea8f76f

Provenance: formalization of a published result. Source: Sipser, Exercise 1.31

For any regular language L and natural number n, the n-th power L^n is regular.
-/

/-- Any power of a regular language is regular. -/
theorem is_regular_pow {α : Type*} {L : Language α} (h : L.IsRegular) (n : ℕ) : (L ^ n).IsRegular := by
  induction n with
  | zero => rw [pow_zero]; exact is_regular_one
  | succ n ih => rw [pow_succ]; exact is_regular_mul ih h
