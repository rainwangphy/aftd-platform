import AFTD.Prelude

/-!
# binary_quartic_relations_decomposable

Topic: quantum   Node: 6dbcd7fd49c0

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

A binary matrix satisfying Qij*Qkl+Qik*Qjl+Qil*Qjk=0 for all four indices can be written Qij=ai*bj+bi*aj.
-/

theorem binary_quartic_relations_decomposable {ι : Type*}
    (Q : Matrix ι ι (ZMod 2))
    (hQ : ∀ i j k l, Q i j * Q k l + Q i k * Q j l + Q i l * Q j k = 0) :
    ∃ a b : ι → ZMod 2, ∀ i j, Q i j = a i * b j + b i * a j := by
  classical
  by_cases hz : Q = 0
  · exact ⟨0, 0, by simp [hz]⟩
  · obtain ⟨k, l, hkl⟩ : ∃ k l, Q k l ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      ext i j
      exact h i j
    have hkl1 : Q k l = 1 := by
      have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      exact (h01 (Q k l)).resolve_left hkl
    refine ⟨fun i => Q i k, fun i => Q i l, ?_⟩
    intro i j
    have h := hQ i j k l
    rw [hkl1, mul_one] at h
    linear_combination (norm := ring_nf) h <;> reduce_mod_char

/- The fourth finite difference of twice a binary quadratic form is
four times its four-variable alternating coefficient. -/
