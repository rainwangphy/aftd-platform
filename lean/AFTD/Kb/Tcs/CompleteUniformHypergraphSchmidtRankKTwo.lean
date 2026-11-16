import AFTD.Prelude

/-!
# complete_uniform_hypergraph_schmidt_rank_k_two

Topic: quantum   Node: 3a467d6a29d2

Provenance: formalization of a published result. Source: OP-1672

For any positive integers a and b, the rank over the rationals of the (a + 1) by (b + 1) matrix with entries (-1)^(Nat.choose (i + j) 2) for 0 ≤ i ≤ a and 0 ≤ j ≤ b is equal to 2.
-/

/-- For k = 2 and any positive integers a and b, the rational rank of the (a+1) x (b+1) complete 2-uniform hypergraph matrix is exactly 2. -/
theorem complete_uniform_hypergraph_schmidt_rank_k_two (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Matrix.rank (fun (i : Fin (a + 1)) (j : Fin (b + 1)) => (-1 : ℚ) ^ (Nat.choose (i.val + j.val) 2)) = 2 := by
  let c : ℕ → ℚ := fun n => (-1 : ℚ) ^ (Nat.choose n 2)
  have hrec2 : ∀ n, c (n+2) = - c n := by
    intro n
    dsimp [c]
    have hchoose : Nat.choose (n+2) 2 = Nat.choose n 2 + (2*n+1) := by
      calc
        Nat.choose (n+2) 2 = (n+1).choose 1 + (n+1).choose 2 := by
          rw [show n+2 = (n+1)+1 by omega, Nat.choose_succ_succ']
        _ = (n+1) + ((n).choose 1 + (n).choose 2) := by
          rw [Nat.choose_one_right, Nat.choose_succ_succ']
        _ = Nat.choose n 2 + (2*n+1) := by
          rw [Nat.choose_one_right]
          ring
    rw [hchoose, pow_add]
    have hodd : Odd (2*n+1) := odd_two_mul_add_one n
    rw [hodd.neg_one_pow]
    ring
  have hid : ∀ i j, c (i+j) = ((c i + c (i+1))/2) * c j + ((c i - c (i+1))/2) * c (j+1) := by
    intro i
    refine Nat.twoStepInduction (motive := fun n => ∀ j, c (n+j) = ((c n + c (n+1))/2) * c j + ((c n - c (n+1))/2) * c (j+1)) ?_ ?_ ?_ i
    · intro j
      simp [c]
    · intro j
      dsimp [c]
      rw [show 1 + j = j + 1 by omega]
      norm_num
    · intro n ihn ihs j
      rw [show n + 2 + j = (n + j) + 2 by omega, hrec2 (n+j), ihn j]
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, hrec2 (n+1), hrec2 n]
      ring
  let M : Matrix (Fin (a+1)) (Fin (b+1)) ℚ := fun i j => c (i.val + j.val)
  change M.rank = 2
  let A : Matrix (Fin (a+1)) (Fin 2) ℚ := fun i k =>
    if k = 0 then (c i.val + c (i.val+1))/2 else (c i.val - c (i.val+1))/2
  let B : Matrix (Fin 2) (Fin (b+1)) ℚ := fun k j =>
    if k = 0 then c j.val else c (j.val+1)
  have hAB : M = A * B := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [M, A, B]
    exact hid i.val j.val
  have hrank_le : M.rank ≤ 2 := by
    rw [hAB]
    calc
      (A * B).rank ≤ A.rank := Matrix.rank_mul_le_left A B
      _ ≤ Fintype.card (Fin 2) := Matrix.rank_le_card_width A
      _ = 2 := by simp
  let r : Fin 2 → Fin (a+1) := Fin.castLE (by omega)
  let s : Fin 2 → Fin (b+1) := Fin.castLE (by omega)
  have hNdet : (M.submatrix r s).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    dsimp only [Matrix.submatrix, M, c]
    simp only [r, s, Fin.val_castLE]
    norm_num
  have hNrank : (M.submatrix r s).rank = 2 := by
    rw [Matrix.rank_of_det_ne_zero hNdet]
    simp
  have hrank_ge : 2 ≤ M.rank := by
    calc
      2 = (M.submatrix r s).rank := hNrank.symm
      _ ≤ M.rank := Matrix.rank_submatrix_le M r s
  omega
