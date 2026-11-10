import AFTD.Prelude

/-!
# matrix_block_det_card_sum_le_width

Topic: combinatorics   Node: 7b8380b68075

Provenance: helper lemma. arXiv:2611.12199, proof of Theorem 1.7 (block-diagonal rank count)

Let K be a field, L a matrix with rows indexed by a finite type ι and columns by a finite type κ, and R a matrix with rows indexed by κ and columns by ι. Let A_1, ..., A_t be finite subsets of ι such that the product L*R vanishes at (a, b) whenever a lies in A_i and b in A_j with i ≠ j, and such that each principal submatrix of L*R on A_i has nonzero determinant. Then the sizes of the A_i sum to at most the cardinality of κ.
-/

/-- Rank counting: nonsingular principal blocks of a block-diagonal restriction of a product L*R through κ have total size at most |κ|. -/
theorem matrix_block_det_card_sum_le_width {K : Type*} [Field K] {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] {t : ℕ} (L : Matrix ι κ K) (R : Matrix κ ι K)
    (𝒜 : Fin t → Finset ι)
    (hzero : ∀ i j, i ≠ j → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, (L * R) a b = 0)
    (hdet : ∀ i, ((L * R).submatrix (fun x : 𝒜 i => (x : ι)) (fun x : 𝒜 i => (x : ι))).det ≠ 0) :
    ∑ i, (𝒜 i).card ≤ Fintype.card κ := by
  classical
  set N : Matrix (Σ i, 𝒜 i) (Σ i, 𝒜 i) K := fun x y => (L * R) x.2 y.2 with hN
  have hblk : N = Matrix.blockDiagonal'
      (fun i => (L * R).submatrix (fun x : 𝒜 i => (x : ι)) (fun x : 𝒜 i => (x : ι))) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst h
      simp [hN, Matrix.blockDiagonal'_apply_eq]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact hzero i j h a a.2 b b.2
  have hunitN : IsUnit N.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := Matrix.blockDiagonal' (fun i =>
      ((L * R).submatrix (fun x : 𝒜 i => (x : ι)) (fun x : 𝒜 i => (x : ι)))⁻¹)) ?_
    rw [hblk, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_one]
    congr 1
    funext i
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet i))
  have hfac : N = Matrix.of (fun (x : Σ i, 𝒜 i) k => L x.2 k) *
      Matrix.of (fun k (y : Σ i, 𝒜 i) => R k y.2) := by
    ext x y
    simp [hN, Matrix.mul_apply]
  have hrank : N.rank = Fintype.card (Σ i, 𝒜 i) :=
    Matrix.rank_of_isUnit N ((Matrix.isUnit_iff_isUnit_det N).mpr hunitN)
  have hle : N.rank ≤ Fintype.card κ := by
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  rw [hrank, Fintype.card_sigma] at hle
  simpa using hle
