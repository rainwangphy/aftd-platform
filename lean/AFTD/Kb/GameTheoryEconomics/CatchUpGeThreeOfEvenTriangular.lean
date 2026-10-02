import AFTD.Prelude

/-!
# catch_up_ge_three_of_even_triangular

Topic: combinatorial_games   Node: 94f04ef956ed

If N > 0 and the triangular number N(N+1)/2 is even, then N ≥ 3.
-/

/-- If N > 0 and the triangular number N(N+1)/2 is even, then N ≥ 3. -/
theorem catch_up_ge_three_of_even_triangular (N : ℕ) (hN : 0 < N) (h_even : Even (N * (N + 1) / 2)) :
    3 ≤ N := by
  by_contra! h
  interval_cases N <;> revert h_even <;> decide
