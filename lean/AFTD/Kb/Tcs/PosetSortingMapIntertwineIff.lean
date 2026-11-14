import AFTD.Prelude
import AFTD.Kb.Tcs.PosetSortingMap

/-!
# poset_sorting_map_intertwine_iff

Topic: combinatorics   Node: 4858d373b519

Provenance: helper lemma. Step of arXiv:2611.15540, Theorem A (Theorem 2.1 and Corollary 2.2)

An equivalence e : P ≃ Q between partially ordered sets intertwines R_P and R_Q, (e×e)∘R_P = R_Q∘(e×e), iff e preserves and reflects the strict order.
-/

open Classical in
private lemma psm_apply_it {P : Type*} [PartialOrder P] (p : P × P) :
    poset_sorting_map P p = if p.2 < p.1 then (p.2, p.1) else p := by
  rfl

theorem poset_sorting_map_intertwine_iff {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃ Q) :
    Prod.map e e ∘ poset_sorting_map P = poset_sorting_map Q ∘ Prod.map e e ↔
      ∀ x y : P, e y < e x ↔ y < x := by
  constructor
  · intro h x y
    have hxy := congrFun h (x, y)
    simp only [Function.comp_apply, psm_apply_it, Prod.map] at hxy
    by_cases hq : x = y
    · subst hq; simp
    have hne : e x ≠ e y := fun h' => hq (e.injective h')
    by_cases h1 : y < x <;> by_cases h2 : e y < e x
    · exact iff_of_true h2 h1
    · rw [if_pos h1, if_neg h2] at hxy
      exact absurd (Prod.ext_iff.1 hxy).2 hne
    · rw [if_neg h1, if_pos h2] at hxy
      exact absurd (Prod.ext_iff.1 hxy).1 hne
    · exact iff_of_false h2 h1
  · intro h
    funext ⟨x, y⟩
    simp only [Function.comp_apply, psm_apply_it, Prod.map]
    split_ifs <;> simp_all
