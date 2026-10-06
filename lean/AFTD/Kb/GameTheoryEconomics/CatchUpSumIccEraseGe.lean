import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpSumIccId

/-!
# catch_up_sum_icc_erase_ge

Topic: combinatorial_games   Node: 1beffc4536b0

Provenance: helper lemma. step towards the Catch-Up conjecture (Catch-Up: A Game in Which the Lead Alternates (Game & Puzzle Design 1(2), 2015), Sec. 3.1; formal-conjectures CatchUpConjecture.lean) (Catch-Up ladder step)

In {1, ..., N} with even triangular sum, removing any element x leaves a sum at least x.
-/

/-- For any N with even triangular number and any x in {1, ..., N}, the sum of the remaining elements {1, ..., N} \ {x} is at least x. -/
theorem catch_up_sum_icc_erase_ge (N : ℕ) (h_even : Even (N * (N + 1) / 2))
    (x : ℕ) (hx : x ∈ Finset.Icc 1 N) :
    x ≤ ∑ y ∈ (Finset.Icc 1 N).erase x, y := by
  have hx_le : x ≤ N := (Finset.mem_Icc.mp hx).2
  have hN : 3 ≤ N := by
    rcases N with _ | _ | _ | N'
    · have := (Finset.mem_Icc.mp hx).1
      omega
    · revert h_even; decide
    · revert h_even; decide
    · omega
  have h_le : 2 * x ≤ N * (N + 1) / 2 := by
    have : 4 * N ≤ N * (N + 1) := by
      calc 4 * N ≤ (N + 1) * N := Nat.mul_le_mul_right N (by omega)
      _ = N * (N + 1) := mul_comm (N + 1) N
    omega
  have h_sum : x + ∑ y ∈ (Finset.Icc 1 N).erase x, y = N * (N + 1) / 2 := by
    rw [← catch_up_sum_icc_id N]
    exact Finset.add_sum_erase (Finset.Icc 1 N) (fun y => y) hx
  omega
