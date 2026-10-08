import AFTD.Prelude

/-!
# matrix_permanent_from_blocks_zero_one_two

Topic: algebraic_complexity   Node: 7831db20f497

Provenance: original. Related work: Mathlib.LinearAlgebra.Matrix.Block

For any commutative semiring R and any square matrices A over m and D over n, the permanent of the block matrix with A in the top-left, 0 in the top-right, C in the bottom-left, and D in the bottom-right equals the permanent of A times the permanent of D.
-/

theorem matrix_permanent_from_blocks_zero_one_two_zero_two_one
    {m n R : Type*} [DecidableEq m] [DecidableEq n] [Fintype m]
    [Fintype n] [CommSemiring R] (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp_rw [Matrix.permanent]
  convert!
    Eq.symm <|
      Finset.sum_subset (M := R) (Finset.subset_univ ((Equiv.Perm.sumCongrHom m n).range : Set (Equiv.Perm (m ⊕ n))).toFinset) ?_
  · simp_rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    refine Finset.sum_nbij (fun σ ↦ σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
    · intro σ₁₂ _
      rw [Set.mem_toFinset]
      exact ⟨σ₁₂, rfl⟩
    · intro σ₁ _ σ₂ _
      dsimp only
      intro h
      have h2 : ∀ x, Equiv.Perm.sumCongr σ₁.fst σ₁.snd x = Equiv.Perm.sumCongr σ₂.fst σ₂.snd x :=
        DFunLike.congr_fun h
      simp only [Sum.map_inr, Sum.map_inl, Equiv.Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
        Sum.inr.injEq] at h2
      ext x
      · exact h2.left x
      · exact h2.right x
    · intro σ hσ
      rw [Finset.mem_coe, Set.mem_toFinset] at hσ
      obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
      use σ₁₂
      rw [← hσ₁₂]
      simp
    · simp only [forall_prop_of_true, Prod.forall, Finset.mem_univ]
      intro σ₁ σ₂
      rw [Fintype.prod_sum_type]
      simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₂]
  · rintro σ - hσn
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      rw [Set.mem_toFinset] at hσn
      simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
        mt Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
    obtain ⟨a, ha⟩ := not_forall.mp h1
    rcases hx : σ (Sum.inl a) with a2 | b
    · have hn := (not_exists.mp ha) a2
      exact absurd hx.symm hn
    · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))]
      rw [hx, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The permanent of a block lower-triangular matrix is the product of the permanents of the diagonal blocks. -/
theorem matrix_permanent_from_blocks_zero_one_two {m n R : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [CommSemiring R] (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R) : (Matrix.fromBlocks A 0 C D).permanent = A.permanent * D.permanent := by
  rw [← Matrix.permanent_transpose, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    matrix_permanent_from_blocks_zero_one_two_zero_two_one, Matrix.permanent_transpose,
    Matrix.permanent_transpose]
