import AFTD.Prelude

/-!
# monochromatic_matching_five_cycle_obstruction

Topic: combinatorics   Node: 4ed4bfd3af80

Provenance: helper lemma. General five-cycle obstruction behind the fixed matching-cut counterexample for OP-874, arXiv:2610.41950; disjoint exposed sets are the local compatibility condition of Section 2.

A cyclic sequence of five compatible local states cannot have the same low external color at all five vertices while the five cycle edges use only four high colors: each vertex has three distinct internal colors missing its external palette, adjacent exposed sets are disjoint, and neighboring cycle-edge labels are distinct.
-/

set_option maxHeartbeats 5000000

private theorem three_distinct_avoid_two_test {Ω : Type*} (x y z a b : Ω)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ t, (t = x ∨ t = y ∨ t = z) ∧ t ≠ a ∧ t ≠ b := by
  classical
  by_contra H
  push_neg at H
  have hx : x = a ∨ x = b := by by_cases h : x = a; exact Or.inl h; exact Or.inr (H x (Or.inl rfl) h)
  have hy : y = a ∨ y = b := by by_cases h : y = a; exact Or.inl h; exact Or.inr (H y (Or.inr (Or.inl rfl)) h)
  have hz : z = a ∨ z = b := by by_cases h : z = a; exact Or.inl h; exact Or.inr (H z (Or.inr (Or.inr rfl)) h)
  grind

private theorem five_cycle_four_colors_impossible_test (t : Fin 5 → Fin 4)
    (hnear : ∀ i, t i ≠ t (i + 1)) (hfar : ∀ i, t i ≠ t (i + 2)) : False := by
  have hcover : ∀ i j : Fin 5, i ≠ j →
      j = i + 1 ∨ j = i + 2 ∨ i = j + 1 ∨ i = j + 2 := by decide
  have hi : Function.Injective t := by
    intro i j ht
    by_contra hij
    rcases hcover i j hij with h | h | h | h
    · exact hnear i (by simpa [h] using ht)
    · exact hfar i (by simpa [h] using ht)
    · exact hnear j (by simpa [h] using ht.symm)
    · exact hfar j (by simpa [h] using ht.symm)
  have hc := Fintype.card_le_of_injective t hi
  norm_num at hc

theorem monochromatic_matching_five_cycle_obstruction
    {Ω : Type*} (low : Ω) (high : Fin 4 → Ω) (t : Fin 5 → Fin 4)
    (hiddenF hiddenB : Fin 5 → Ω) (inside : Fin 5 → Fin 3 → Ω)
    (hnear : ∀ i, t i ≠ t (i + 1))
    (hinj : ∀ i, Function.Injective (inside i))
    (hmissing : ∀ i j, inside i j ≠ low ∧
      inside i j ≠ high (t i) ∧ inside i j ≠ high (t (i + 1)))
    (hdisjoint : ∀ i z,
      (z ≠ low ∧ z ≠ high (t i) ∧ z ≠ high (t (i + 1)) ∧ z ≠ hiddenF i) →
      (z ≠ low ∧ z ≠ high (t (i + 1)) ∧ z ≠ high (t (i + 2)) ∧ z ≠ hiddenB (i + 1)) → False) : False := by
  have hfar : ∀ i, t i ≠ t (i + 2) := by
    intro i heq
    have h01 : inside i 0 ≠ inside i 1 := fun h => by have := hinj i h; contradiction
    have h02 : inside i 0 ≠ inside i 2 := fun h => by have := hinj i h; contradiction
    have h12 : inside i 1 ≠ inside i 2 := fun h => by have := hinj i h; contradiction
    obtain ⟨z, hz, hzF, hzB⟩ := three_distinct_avoid_two_test (inside i 0) (inside i 1) (inside i 2) (hiddenF i) (hiddenB (i+1)) h01 h02 h12
    have hm : z ≠ low ∧ z ≠ high (t i) ∧ z ≠ high (t (i + 1)) := by
      rcases hz with rfl | rfl | rfl
      · exact hmissing i 0
      · exact hmissing i 1
      · exact hmissing i 2
    apply hdisjoint i z
    · exact ⟨hm.1, hm.2.1, hm.2.2, hzF⟩
    · exact ⟨hm.1, hm.2.2, by simpa [heq] using hm.2.1, hzB⟩
  exact five_cycle_four_colors_impossible_test t hnear hfar
