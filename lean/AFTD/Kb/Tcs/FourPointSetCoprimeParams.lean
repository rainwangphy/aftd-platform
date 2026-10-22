import AFTD.Prelude

/-!
# four_point_set_coprime_params

Topic: combinatorics   Node: d6656dcfc25d

Provenance: helper lemma. arXiv:2610.24281 Lemma 3.2

For any integer n, the integers a = 2n - 1 and 2b = 2(2n + 1) are coprime.
-/

/-- The parameters a = 2n - 1 and 2b = 2(2n + 1) are coprime for any integer n. -/
theorem four_point_set_coprime_params (n : ℤ) :
    let a : ℤ := 2 * n - 1
    let b : ℤ := 2 * n + 1
    IsCoprime a (2 * b) := by
  intro a b
  rw [IsCoprime.mul_right_iff]
  refine ⟨⟨-1, n, ?_⟩, ⟨-(n + 1), n, ?_⟩⟩
  · dsimp only [a]
    ring
  · dsimp only [a, b]
    ring
