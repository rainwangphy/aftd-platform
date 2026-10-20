import AFTD.Prelude
import AFTD.Kb.NumberTheory.Op153SquareDiffFreeFourCardLeTwo

/-!
# op_153_square_diff_free_five_card_le_two

Topic: elementary_number_theory   Node: d4526efaf68e

Provenance: helper lemma. arXiv:2610.07765 Corollary 1.2 -- A new bound for the Furstenberg--Sárközy theorem using the van der Corput property

Every subset $A \subseteq \{1, 2, 3, 4, 5\}$ whose distinct elements have difference not equal to $n^2$ for any positive integer $n$ has cardinality at most 2.
-/

/-- Every square-difference-free subset of {1, 2, 3, 4, 5} has cardinality at most 2. -/
theorem op_153_square_diff_free_five_card_le_two
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 5)
    (hdiff : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ n : ℕ, 0 < n ∧ (a : ℤ) - b = (Polynomial.X ^ 2 : Polynomial ℤ).eval (n : ℤ)) :
    A.card ≤ 2 := by
  by_cases h5 : 5 ∈ A
  · by_cases h2 : 2 ∈ A
    · have hsub : A ⊆ ({2, 5} : Finset ℕ) := by
        have h1not : 1 ∉ A := by
          intro h1
          exact hdiff 5 h5 1 h1 (by norm_num) ⟨2, by norm_num, by norm_num⟩
        have h3not : 3 ∉ A := by
          intro h3
          exact hdiff 3 h3 2 h2 (by norm_num) ⟨1, by norm_num, by norm_num⟩
        have h4not : 4 ∉ A := by
          intro h4
          exact hdiff 5 h5 4 h4 (by norm_num) ⟨1, by norm_num, by simp⟩
        intro x hx
        have hx15 : x ∈ Finset.Icc 1 5 := hA hx
        rw [Finset.mem_Icc] at hx15
        have hxlow : 1 ≤ x := hx15.1
        have hxup : x ≤ 5 := hx15.2
        interval_cases x <;> simp_all
      exact le_trans (Finset.card_le_card hsub) (by simp)
    · have hsub : A ⊆ ({3, 5} : Finset ℕ) := by
        have h1not : 1 ∉ A := by
          intro h1
          exact hdiff 5 h5 1 h1 (by norm_num) ⟨2, by norm_num, by norm_num⟩
        have h4not : 4 ∉ A := by
          intro h4
          exact hdiff 5 h5 4 h4 (by norm_num) ⟨1, by norm_num, by simp⟩
        intro x hx
        have hx15 : x ∈ Finset.Icc 1 5 := hA hx
        rw [Finset.mem_Icc] at hx15
        have hxlow : 1 ≤ x := hx15.1
        have hxup : x ≤ 5 := hx15.2
        interval_cases x <;> simp_all
      exact le_trans (Finset.card_le_card hsub) (by simp)
  · have hA4 : A ⊆ Finset.Icc 1 4 := by
      intro x hx
      have hx15 : x ∈ Finset.Icc 1 5 := hA hx
      rw [Finset.mem_Icc] at hx15 ⊢
      have hx5 : x ≠ 5 := by
        intro h
        apply h5
        simpa [h] using hx
      omega
    exact op_153_square_diff_free_four_card_le_two A hA4 hdiff
