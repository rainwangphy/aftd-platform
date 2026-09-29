import AFTD.Prelude

/-!
# divide_and_conquer_unequal_roots_recurrence

Topic: algorithms   Node: b428b71b69a9

For real branching factor a and cost ratio r with a != r, base value d and cost scale c, the recurrence T(k+1) = a*T(k) + c*r^(k+1) with T(0) = d has exact solution T(k) = d*a^k + c*r*(a^k - r^k)/(a - r).
-/

/-- The exact solution of the divide-and-conquer recurrence with unequal roots (a ≠ r), corresponding to Master theorem cases 1 and 3. -/
theorem divide_and_conquer_unequal_roots_recurrence
    (T : ℕ → ℝ) (a r c d : ℝ) (har : a ≠ r)
    (h0 : T 0 = d)
    (hrec : ∀ k : ℕ, T (k + 1) = a * T k + c * r ^ (k + 1)) :
    ∀ k : ℕ, T k = d * a ^ k + c * r * ((a ^ k - r ^ k) / (a - r)) := by
  intro k
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    rw [hrec, ih]
    have h_sub : a - r ≠ 0 := sub_ne_zero.mpr har
    rw [pow_succ a k, pow_succ r k]
    field_simp
    ring
