import AFTD.Prelude

/-!
# op_153_square_diff_free_four_card_le_two

Topic: elementary_number_theory   Node: 51009d3a6926

Provenance: helper lemma. arXiv:2610.07765 Corollary 1.2 -- A new bound for the Furstenberg--Sárközy theorem using the van der Corput property

Every subset $A \subseteq \{1, 2, 3, 4\}$ whose distinct elements have difference not equal to $n^2$ for any positive integer $n$ has cardinality at most 2.
-/

/-- Every square-difference-free subset of {1, 2, 3, 4} has cardinality at most 2. -/
theorem op_153_square_diff_free_four_card_le_two
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 4)
    (hdiff : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ n : ℕ, 0 < n ∧ (a : ℤ) - b = (Polynomial.X ^ 2 : Polynomial ℤ).eval (n : ℤ)) :
    A.card ≤ 2 := by
  let f : ℕ → ℕ := fun x => (x + 1) / 2
  have hno : ∀ a ∈ A, a + 1 ∈ A → False := by
    intro a ha ha1
    have h := hdiff (a + 1) ha1 a ha (by omega)
    apply h
    refine ⟨1, by norm_num, ?_⟩
    simp
  have hmap : Set.MapsTo f ↑A ↑({1, 2} : Finset ℕ) := by
    intro a ha
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    have ha' := hA ha
    simp only [Finset.mem_Icc] at ha'
    have ha1 : 1 ≤ a := ha'.1
    have ha4 : a ≤ 4 := ha'.2
    interval_cases a <;> norm_num [f]
  have hinj : Set.InjOn f ↑A := by
    intro a ha b hb hfab
    by_contra hne
    have ha' := hA ha
    have hb' := hA hb
    simp only [Finset.mem_Icc] at ha' hb'
    have ha1 : 1 ≤ a := ha'.1
    have ha4 : a ≤ 4 := ha'.2
    have hb1 : 1 ≤ b := hb'.1
    have hb4 : b ≤ 4 := hb'.2
    interval_cases a <;> interval_cases b <;> simp_all [f]
  exact Finset.card_le_card_of_injOn f hmap hinj
