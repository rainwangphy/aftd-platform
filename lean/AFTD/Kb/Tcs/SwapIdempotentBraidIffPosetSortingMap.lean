import AFTD.Prelude
import AFTD.Kb.Tcs.PosetSortingMap
import AFTD.Kb.Tcs.IsBraidSolution
import AFTD.Kb.Tcs.PosetSortingMapIdempotentBraid

/-!
# swap_idempotent_braid_iff_poset_sorting_map

Topic: combinatorics   Node: 07a68d5b2382

Provenance: helper lemma. Step of arXiv:2611.15540, Theorem A (Theorem 2.1 and Corollary 2.2)

If R : X×X → X×X satisfies R(x,y) ∈ {(x,y),(y,x)} for all x,y, then R is an idempotent solution of the braid equation iff R = R_P for a unique partial order on X.
-/

open Classical in
private lemma psm_apply_sw {P : Type*} [PartialOrder P] (p : P × P) :
    poset_sorting_map P p = if p.2 < p.1 then (p.2, p.1) else p := by
  rfl

theorem swap_idempotent_braid_iff_poset_sorting_map {X : Type*} (R : X × X → X × X)
    (hR : ∀ x y : X, R (x, y) = (x, y) ∨ R (x, y) = (y, x)) :
    (is_braid_solution R ∧ R ∘ R = R) ↔ ∃! o : PartialOrder X, R = @poset_sorting_map X o := by
  constructor
  · rintro ⟨hb, hi⟩
    have idem : ∀ p, R (R p) = R p := fun p => congrFun hi p
    have asymm : ∀ a b : X, (b ≠ a ∧ R (b, a) = (a, b)) → ¬ (a ≠ b ∧ R (a, b) = (b, a)) := by
      rintro a b ⟨hne, h1⟩ ⟨-, h2⟩
      have := idem (b, a)
      rw [h1, h2] at this
      exact hne (Prod.ext_iff.1 this).1
    have trans : ∀ a b c : X, (b ≠ a ∧ R (b, a) = (a, b)) → (c ≠ b ∧ R (c, b) = (b, c)) →
        (c ≠ a ∧ R (c, a) = (a, c)) := by
      rintro a b c ⟨hba, h1⟩ ⟨hcb, h2⟩
      have hca : c ≠ a := by
        rintro rfl
        exact asymm _ _ ⟨hba, h1⟩ ⟨hcb, h2⟩
      refine ⟨hca, ?_⟩
      rcases hR c a with h3 | h3
      · exfalso
        have hbc : R (b, c) = (b, c) := by have := idem (c, b); rwa [h2] at this
        have hab : R (a, b) = (a, b) := by have := idem (b, a); rwa [h1] at this
        have := congrFun hb (c, b, a)
        simp only [Function.comp_apply, h1, h2, h3, hbc, hab] at this
        exact hcb (Prod.ext_iff.1 this).1.symm
      · exact h3
    refine ⟨{ le := fun a b => a = b ∨ (b ≠ a ∧ R (b, a) = (a, b))
              lt := fun a b => b ≠ a ∧ R (b, a) = (a, b)
              le_refl := fun a => Or.inl rfl
              le_trans := by
                rintro a b c (rfl | hab) (rfl | hbc)
                · exact Or.inl rfl
                · exact Or.inr hbc
                · exact Or.inr hab
                · exact Or.inr (trans a b c hab hbc)
              lt_iff_le_not_ge := by
                intro a b
                constructor
                · intro h
                  refine ⟨Or.inr h, ?_⟩
                  rintro (rfl | h')
                  · exact h.1 rfl
                  · exact asymm a b h h'
                · rintro ⟨rfl | h, h'⟩
                  · exact absurd (Or.inl rfl) h'
                  · exact h
              le_antisymm := by
                rintro a b (rfl | hab) (h | hba)
                · rfl
                · rfl
                · exact h.symm
                · exact absurd hba (asymm a b hab) }, ?_, ?_⟩
    · funext ⟨x, y⟩
      dsimp only [poset_sorting_map]
      split_ifs with h
      · exact h.2
      · rcases hR x y with h' | h'
        · exact h'
        · by_cases hxy : x = y
          · subst hxy; exact h'
          · exact absurd ⟨hxy, h'⟩ h
    · intro o' ho'
      apply PartialOrder.ext_lt
      intro a b
      show a < b ↔ (b ≠ a ∧ R (b, a) = (a, b))
      have := congrFun ho' (b, a)
      rw [psm_apply_sw] at this
      dsimp only at this
      constructor
      · intro h
        rw [if_pos h] at this
        exact ⟨h.ne', this⟩
      · rintro ⟨hne, h⟩
        by_contra hlt
        rw [if_neg hlt, h] at this
        exact hne (Prod.ext_iff.1 this).2
  · rintro ⟨o, rfl, -⟩
    exact (@poset_sorting_map_idempotent_braid X o)
