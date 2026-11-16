import AFTD.Prelude

/-!
# complete_uniform_hypergraph_schmidt_rank_k_eq_add

Topic: quantum   Node: d328b3218320

Provenance: formalization of a published result. Source: OP-1672

For any positive integers a and b, when k = a + b, the rank over the rationals of the (a + 1) by (b + 1) matrix with entries (-1)^(Nat.choose (i + j) (a + b)) for 0 ≤ i ≤ a and 0 ≤ j ≤ b is equal to 2.
-/

/-- For k = a + b and any positive integers a and b, the rational rank of the (a+1) x (b+1) complete (a+b)-uniform hypergraph matrix is exactly 2. -/
theorem complete_uniform_hypergraph_schmidt_rank_k_eq_add (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Matrix.rank (fun (i : Fin (a + 1)) (j : Fin (b + 1)) => (-1 : ℚ) ^ (Nat.choose (i.val + j.val) (a + b))) = 2 := by
  classical
  have hrank_add_le : ∀ {X Y : Type} [Fintype Y] (A B : Matrix X Y ℚ),
      (A + B).rank ≤ A.rank + B.rank := by
    intro X Y _ A B
    rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
    exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)
  set M : Matrix (Fin (a+1)) (Fin (b+1)) ℚ := fun i j => (-1:ℚ) ^ (Nat.choose (i.val+j.val) (a+b)) with hM
  change Matrix.rank M = 2
  let u : Fin (a+1) → ℚ := fun i => if i.val = a then -2 else 0
  let v : Fin (b+1) → ℚ := fun j => if j.val = b then 1 else 0
  have hchoose : ∀ (i : Fin (a+1)) (j : Fin (b+1)), M i j = 1 + u i * v j := by
    intro i j
    rw [hM]
    dsimp only [u, v]
    have hi : i.val ≤ a := Nat.lt_succ_iff.mp i.isLt
    have hj : j.val ≤ b := Nat.lt_succ_iff.mp j.isLt
    have hle : i.val + j.val ≤ a + b := Nat.add_le_add hi hj
    have hiff : i.val + j.val = a + b ↔ i.val = a ∧ j.val = b := by omega
    by_cases h : i.val = a ∧ j.val = b
    · have hsum : i.val + j.val = a + b := hiff.mpr h
      have hch : Nat.choose (i.val + j.val) (a + b) = 1 := by rw [hsum, Nat.choose_self]
      rw [hch]
      rw [if_pos h.1, if_pos h.2]
      norm_num
    · have hsum_ne : i.val + j.val ≠ a + b := fun hs => h (hiff.mp hs)
      have hlt : i.val + j.val < a + b := lt_of_le_of_ne hle hsum_ne
      have hch : Nat.choose (i.val + j.val) (a + b) = 0 := Nat.choose_eq_zero_of_lt hlt
      have hprod : (if i.val = a then (-2 : ℚ) else 0) * (if j.val = b then (1 : ℚ) else 0) = 0 := by
        by_cases h1 : i.val = a
        · have h2 : j.val ≠ b := fun h2 => h ⟨h1, h2⟩
          rw [if_pos h1, if_neg h2]; norm_num
        · rw [if_neg h1]; norm_num
      rw [hch, hprod]
      norm_num
  have hupper : Matrix.rank M ≤ 2 := by
    have hM_eq : M = Matrix.vecMulVec (fun _ : Fin (a+1) => (1:ℚ)) (fun _ : Fin (b+1) => (1:ℚ)) +
        (Matrix.vecMulVec u v : Matrix (Fin (a+1)) (Fin (b+1)) ℚ) := by
      ext i j
      rw [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, hchoose]
      norm_num
    rw [hM_eq]
    have h2 := hrank_add_le (Matrix.vecMulVec (fun _ : Fin (a+1) => (1:ℚ)) (fun _ : Fin (b+1) => (1:ℚ)))
      (Matrix.vecMulVec u v : Matrix (Fin (a+1)) (Fin (b+1)) ℚ)
    have h3 : (Matrix.vecMulVec (fun _ : Fin (a+1) => (1:ℚ)) (fun _ : Fin (b+1) => (1:ℚ)) : Matrix (Fin (a+1)) (Fin (b+1)) ℚ).rank ≤ 1 :=
      Matrix.rank_vecMulVec_le _ _
    have h4 : (Matrix.vecMulVec u v : Matrix (Fin (a+1)) (Fin (b+1)) ℚ).rank ≤ 1 :=
      Matrix.rank_vecMulVec_le _ _
    omega
  have hlower : 2 ≤ Matrix.rank M := by
    let r : Fin 2 → Fin (a+1) := ![0, ⟨a, Nat.lt_succ_self a⟩]
    let c : Fin 2 → Fin (b+1) := ![0, ⟨b, Nat.lt_succ_self b⟩]
    have hsub : (M.submatrix r c).rank = 2 := by
      apply Matrix.rank_of_det_ne_zero
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply]
      rw [hchoose, hchoose, hchoose, hchoose]
      simp only [r, c, Matrix.cons_val_zero, Matrix.cons_val_one, u, v]
      simp [show ¬ (0:ℕ) = a by omega, show ¬ (0:ℕ) = b by omega]
    have hle := Matrix.rank_submatrix_le M r c
    omega
  omega
