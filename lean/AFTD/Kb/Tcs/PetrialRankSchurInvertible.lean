import AFTD.Prelude

/-!
# petrial_rank_schur_invertible

Topic: combinatorics   Node: a138a5af7baa

Provenance: helper lemma. Block elimination for the leaf recurrence in OP-1239.

For square finite block matrices over a field, if the upper-left block is invertible, the rank of the whole block matrix is the size of that block plus the rank of its Schur complement.
-/

namespace Op1239Schur
open Matrix
section
variable {K m n : Type*} [Field K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem petrial_kernel_block_identity (D : Matrix n n K) :
    Module.finrank K (LinearMap.ker (Matrix.mulVecLin (Matrix.fromBlocks (1 : Matrix m m K) 0 0 D))) =
      Module.finrank K (LinearMap.ker D.mulVecLin) := by
  let e : LinearMap.ker (Matrix.mulVecLin (Matrix.fromBlocks (1 : Matrix m m K) 0 0 D)) ≃ₗ[K]
      LinearMap.ker D.mulVecLin := {
    toFun := fun x => ⟨fun i => x.1 (Sum.inr i), by
      have hx := x.2
      change Matrix.mulVec (Matrix.fromBlocks (1 : Matrix m m K) 0 0 D) x.1 = 0 at hx
      change D.mulVec (fun i => x.1 (Sum.inr i)) = 0
      funext i
      have hi := congrFun hx (Sum.inr i)
      change (D.mulVec (x.1 ∘ Sum.inr)) i = 0
      simpa [Matrix.fromBlocks_mulVec] using hi⟩
    invFun := fun y => ⟨Sum.elim (fun _ => 0) y.1, by
      have hy := y.2
      change D.mulVec y.1 = 0 at hy
      change Matrix.mulVec (Matrix.fromBlocks (1 : Matrix m m K) 0 0 D) (Sum.elim (fun _ => 0) y.1) = 0
      funext i
      cases i with
      | inl i => simp [Matrix.fromBlocks_mulVec]
      | inr i =>
        have hi := congrFun hy i
        simpa [Matrix.fromBlocks_mulVec] using hi⟩
    left_inv := fun x => by
      apply Subtype.ext
      funext i
      cases i with
      | inl i =>
        have hx := x.2
        change Matrix.mulVec (Matrix.fromBlocks (1 : Matrix m m K) 0 0 D) x.1 = 0 at hx
        have hi := congrFun hx (Sum.inl i)
        simpa [Matrix.fromBlocks_mulVec] using hi.symm
      | inr i => rfl
    right_inv := fun y => by apply Subtype.ext; rfl
    map_add' := fun x y => by apply Subtype.ext; rfl
    map_smul' := fun c x => by apply Subtype.ext; rfl
  }
  exact e.finrank_eq

theorem petrial_rank_block_identity (D : Matrix n n K) :
    (Matrix.fromBlocks (1 : Matrix m m K) 0 0 D).rank = Fintype.card m + D.rank := by
  have he := petrial_kernel_block_identity (m := m) D
  have h₁ := (Matrix.mulVecLin (Matrix.fromBlocks (1 : Matrix m m K) 0 0 D)).finrank_range_add_finrank_ker
  have h₂ := D.mulVecLin.finrank_range_add_finrank_ker
  change (Matrix.fromBlocks (1 : Matrix m m K) 0 0 D).rank + _ = _ at h₁
  change D.rank + _ = _ at h₂
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at h₁ h₂
  omega


theorem petrial_rank_schur_identity (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K) :
    (Matrix.fromBlocks (1 : Matrix m m K) B C D).rank = Fintype.card m + (D - C * B).rank := by
  let L : Matrix (m ⊕ n) (m ⊕ n) K := Matrix.fromBlocks 1 0 C 1
  let R : Matrix (m ⊕ n) (m ⊕ n) K := Matrix.fromBlocks 1 B 0 1
  let M : Matrix (m ⊕ n) (m ⊕ n) K := Matrix.fromBlocks 1 0 0 (D - C * B)
  have hL : IsUnit L.det := by
    dsimp [L]
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hR : IsUnit R.det := by
    dsimp [R]
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  letI : Invertible (1 : Matrix m m K) := invertibleOne
  have hdec : Matrix.fromBlocks (1 : Matrix m m K) B C D = L * M * R := by
    simpa [L, M, R] using Matrix.fromBlocks_eq_of_invertible₁₁ (1 : Matrix m m K) B C D
  rw [hdec, Matrix.rank_mul_eq_left_of_isUnit_det R (L * M) hR,
    Matrix.rank_mul_eq_right_of_isUnit_det L M hL]
  exact petrial_rank_block_identity (D - C * B)



end
end Op1239Schur
open Op1239Schur

/-- Rank reduction by an invertible leading block, used for the one- and two-vertex elimination cases. -/
theorem petrial_rank_schur_invertible {K m n : Type*} [Field K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m m K) [Invertible A] (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K) : (Matrix.fromBlocks A B C D).rank = Fintype.card m + (D - C * ⅟A * B).rank := by
  let T : Matrix (m ⊕ n) (m ⊕ n) K := Matrix.fromBlocks A 0 0 1
  let N : Matrix (m ⊕ n) (m ⊕ n) K := Matrix.fromBlocks 1 (⅟A * B) C D
  have hT : IsUnit T.det := by
    dsimp [T]
    rw [Matrix.det_fromBlocks_zero₁₂]
    simpa using Matrix.isUnit_det_of_invertible A
  have hmul : Matrix.fromBlocks A B C D = T * N := by
    simp [T, N, Matrix.fromBlocks_multiply, Matrix.mul_assoc]
  rw [hmul, Matrix.rank_mul_eq_right_of_isUnit_det T N hT]
  simpa [N, Matrix.mul_assoc] using petrial_rank_schur_identity (⅟A * B) C D
