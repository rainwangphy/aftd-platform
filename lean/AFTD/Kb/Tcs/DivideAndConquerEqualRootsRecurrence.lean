import AFTD.Prelude

/-!
# divide_and_conquer_equal_roots_recurrence

Topic: algorithms   Node: 7ce803c2a01e

For any real branching factor a, base value d and step cost c, the recurrence T(k+1) = a*T(k) + c*a^(k+1) has exact solution T(k) = d*a^k + c*k*a^k.
-/

/-- Closed-form solution to the divide-and-conquer recurrence with equal roots T(k+1) = a * T(k) + c * a^(k+1). -/
theorem divide_and_conquer_equal_roots_recurrence
    (T : ℕ → ℝ) (a c d : ℝ)
    (h0 : T 0 = d)
    (hrec : ∀ k : ℕ, T (k + 1) = a * T k + c * a ^ (k + 1)) :
    ∀ k : ℕ, T k = d * a ^ k + c * (k : ℝ) * a ^ k := by
  intro k
  induction' k with k ih
  · simp [h0]
  · rw [hrec k, ih]
    push_cast
    ring
