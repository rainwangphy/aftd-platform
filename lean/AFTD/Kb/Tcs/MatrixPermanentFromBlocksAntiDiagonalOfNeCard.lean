import AFTD.Prelude

/-!
# matrix_permanent_from_blocks_anti_diagonal_of_ne_card

Topic: algebraic_complexity   Node: f9159a950e90

Provenance: formalization of a published result. Source: Minc, Permanents (1978); Valiant, Completeness classes in algebra (1979)

For any commutative semiring R, any finite types m and n with decidable equality such that the cardinality of m does not equal the cardinality of n, and any matrices B : Matrix m n R and C : Matrix n m R, the permanent of the block matrix Matrix.fromBlocks (0 : Matrix m m R) B C 0 equals 0.
-/

/-- The permanent of a block anti-diagonal matrix with zero diagonal blocks of unequal dimensions vanishes. -/
theorem matrix_permanent_from_blocks_anti_diagonal_of_ne_card {m n R : Type*}
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [CommSemiring R]
    (hm : Fintype.card m ≠ Fintype.card n) (B : Matrix m n R) (C : Matrix n m R) :
    (Matrix.fromBlocks (0 : Matrix m m R) B C 0).permanent = 0 := by
  have h_prod (σ : Equiv.Perm (m ⊕ n)) :
      ∏ i : m ⊕ n, (Matrix.fromBlocks (0 : Matrix m m R) B C 0) (σ i) i = 0 := by
    by_contra h_ne
    have h_none : ∀ x, (Matrix.fromBlocks (0 : Matrix m m R) B C 0) (σ x) x ≠ 0 := by
      intro x hx
      apply h_ne
      exact Finset.prod_eq_zero (Finset.mem_univ x) hx
    have h1 : ∀ i : m, ∃ b : n, σ (Sum.inl i) = Sum.inr b := by
      intro i
      cases h_case : σ (Sum.inl i) with
      | inl a =>
        exfalso
        have h_zero : (Matrix.fromBlocks (0 : Matrix m m R) B C 0) (σ (Sum.inl i)) (Sum.inl i) = 0 := by
          rw [h_case, Matrix.fromBlocks_apply₁₁]
          rfl
        exact h_none (Sum.inl i) h_zero
      | inr b =>
        exact ⟨b, rfl⟩
    have h2 : ∀ j : n, ∃ a : m, σ (Sum.inr j) = Sum.inl a := by
      intro j
      cases h_case : σ (Sum.inr j) with
      | inl a =>
        exact ⟨a, rfl⟩
      | inr b =>
        exfalso
        have h_zero : (Matrix.fromBlocks (0 : Matrix m m R) B C 0) (σ (Sum.inr j)) (Sum.inr j) = 0 := by
          rw [h_case, Matrix.fromBlocks_apply₂₂]
          rfl
        exact h_none (Sum.inr j) h_zero
    let f : m → n := fun i => (h1 i).choose
    have hf : ∀ i, σ (Sum.inl i) = Sum.inr (f i) := fun i => (h1 i).choose_spec
    have h_inj_f : Function.Injective f := by
      intro i₁ i₂ h_eq
      have : σ (Sum.inl i₁) = σ (Sum.inl i₂) := by rw [hf, hf, h_eq]
      exact Sum.inl_injective (σ.injective this)
    have h_le1 : Fintype.card m ≤ Fintype.card n := Fintype.card_le_of_injective f h_inj_f
    let g : n → m := fun j => (h2 j).choose
    have hg : ∀ j, σ (Sum.inr j) = Sum.inl (g j) := fun j => (h2 j).choose_spec
    have h_inj_g : Function.Injective g := by
      intro j₁ j₂ h_eq
      have : σ (Sum.inr j₁) = σ (Sum.inr j₂) := by rw [hg, hg, h_eq]
      exact Sum.inr_injective (σ.injective this)
    have h_le2 : Fintype.card n ≤ Fintype.card m := Fintype.card_le_of_injective g h_inj_g
    exact hm (le_antisymm h_le1 h_le2)
  simp [Matrix.permanent, h_prod]
