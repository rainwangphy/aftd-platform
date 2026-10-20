import AFTD.Prelude

/-!
# finset_sum_eq_three_of_off

Topic: automata   Node: ce87a5241e19

Provenance: helper lemma. step towards pell_prefix_block_step

A finite sum of an ℕ-valued function that vanishes off three distinct points equals the sum of the three values f a + f b + f c.
-/

/-- If `f : ι → ℕ` vanishes off `{a,b,c}` (distinct), then `∑ x, f x = f a + f b + f c`. -/
theorem finset_sum_eq_three_of_off {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : ∀ x, x ≠ a → x ≠ b → x ≠ c → f x = 0) :
    ∑ x, f x = f a + f b + f c := by
  have hs : ({a, b, c} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hs]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton, add_assoc]
      · simp [hbc]
    · simp [hab, hac]
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact h x hx.1 hx.2.1 hx.2.2
