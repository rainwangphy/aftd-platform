import AFTD.Prelude

/-!
# catch_up_sum_icc_id

Topic: combinatorial_games   Node: 29b2f4c6451f

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

The sum of numbers in the interval {1, ..., N} equals the N-th triangular number N(N+1)/2.
-/

lemma catch_up_sum_icc_id_mul_two (N : ℕ) :
    2 * ∑ x ∈ Finset.Icc 1 N, x = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    linarith

/-- The sum of numbers in the interval {1, ..., N} equals the N-th triangular number N(N+1)/2. -/
theorem catch_up_sum_icc_id (N : ℕ) :
    ∑ x ∈ Finset.Icc 1 N, x = N * (N + 1) / 2 := by
  have h := catch_up_sum_icc_id_mul_two N
  omega
