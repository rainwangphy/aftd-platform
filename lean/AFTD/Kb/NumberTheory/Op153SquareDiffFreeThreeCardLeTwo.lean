import AFTD.Prelude

/-!
# op_153_square_diff_free_three_card_le_two

Topic: elementary_number_theory   Node: 3506341d664b

Provenance: helper lemma. arXiv:2610.07765, Sec. 1

Every subset $A \subseteq \{1, 2, 3\}$ whose distinct elements have difference not equal to $n^2$ for any positive integer $n$ has cardinality at most 2.
-/

/-- Any subset of {1, 2, 3} avoiding positive square differences has cardinality at most 2 (OP-153 partial). -/
theorem op_153_square_diff_free_three_card_le_two
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 3)
    (hdiff : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ n : ℕ, 0 < n ∧ (a : ℤ) - b = (Polynomial.X ^ 2 : Polynomial ℤ).eval (n : ℤ)) :
    A.card ≤ 2 := by
  have hsub : A ⊆ ({1, 2, 3} : Finset ℕ) := by
    intro a ha
    have hmem := hA ha
    simp only [Finset.mem_Icc] at hmem
    obtain ⟨hlo, hhi⟩ := hmem
    interval_cases a <;> simp
  by_contra h
  have h3 : 3 ≤ A.card := by omega
  have hle : ({1, 2, 3} : Finset ℕ).card ≤ A.card := by
    have hc : ({1, 2, 3} : Finset ℕ).card = 3 := by decide
    omega
  have heq : A = ({1, 2, 3} : Finset ℕ) := Finset.eq_of_subset_of_card_le hsub hle
  have h1 : (1:ℕ) ∈ A := by rw [heq]; simp
  have h2 : (2:ℕ) ∈ A := by rw [heq]; simp
  have hne : (2:ℕ) ≠ 1 := by norm_num
  exact hdiff 2 h2 1 h1 hne ⟨1, by norm_num, by norm_num⟩
