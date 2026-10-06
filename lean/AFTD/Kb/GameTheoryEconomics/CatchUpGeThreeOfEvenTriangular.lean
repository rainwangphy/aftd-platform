import AFTD.Prelude

/-!
# catch_up_ge_three_of_even_triangular

Topic: combinatorial_games   Node: 94f04ef956ed

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

If N > 0 and the triangular number N(N+1)/2 is even, then N ≥ 3.
-/

/-- If N > 0 and the triangular number N(N+1)/2 is even, then N ≥ 3. -/
theorem catch_up_ge_three_of_even_triangular (N : ℕ) (hN : 0 < N) (h_even : Even (N * (N + 1) / 2)) :
    3 ≤ N := by
  by_contra! h
  interval_cases N <;> revert h_even <;> decide
