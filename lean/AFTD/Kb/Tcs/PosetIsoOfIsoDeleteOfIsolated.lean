import AFTD.Prelude
import AFTD.Kb.Tcs.PosetHypomorphic

/-!
# poset_iso_of_iso_delete_of_isolated

Topic: combinatorics   Node: fe217eef517e

Provenance: helper lemma. step towards poset_height_one_reconstructible

If x ∈ P and y ∈ Q are each incomparable with every other element and the complements P − x and Q − y are order-isomorphic, then P ≅ Q.
-/

/-- An order isomorphism of the complements of two isolated points extends to an isomorphism of the whole ordered sets. -/
theorem poset_iso_of_iso_delete_of_isolated (P Q : Type) [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q] (x : P) (y : Q) (hx : ∀ z : P, ¬ (x < z ∨ z < x)) (hy : ∀ z : Q, ¬ (y < z ∨ z < y)) (e : {z : P // z ≠ x} ≃o {z : Q // z ≠ y}) : Nonempty (P ≃o Q) := by
  classical
  have hxle : ∀ z : P, x ≤ z ↔ x = z := by
    intro z
    exact ⟨fun h => (lt_or_eq_of_le h).elim (fun hlt => absurd hlt (fun hh => (hx z) (Or.inl hh))) (fun he => he),
           fun h => le_of_eq h⟩
  have hxge : ∀ z : P, z ≤ x ↔ z = x := by
    intro z
    exact ⟨fun h => (lt_or_eq_of_le h).elim (fun hlt => absurd hlt (fun hh => (hx z) (Or.inr hh))) (fun he => he),
           fun h => le_of_eq h⟩
  have hyle : ∀ z : Q, y ≤ z ↔ y = z := by
    intro z
    exact ⟨fun h => (lt_or_eq_of_le h).elim (fun hlt => absurd hlt (fun hh => (hy z) (Or.inl hh))) (fun he => he),
           fun h => le_of_eq h⟩
  have hyge : ∀ z : Q, z ≤ y ↔ z = y := by
    intro z
    exact ⟨fun h => (lt_or_eq_of_le h).elim (fun hlt => absurd hlt (fun hh => (hy z) (Or.inr hh))) (fun he => he),
           fun h => le_of_eq h⟩
  let f : P → Q := fun z => if h : z = x then y else e ⟨z, h⟩
  have hf_x : f x = y := by simp [f]
  have hf_ne : ∀ z (hz : z ≠ x), f z = e ⟨z, hz⟩ := by intro z hz; simp only [f, dif_neg hz]
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a = x
    · by_cases hb : b = x
      · rw [ha, hb]
      · have hfa : f a = y := by rw [ha, hf_x]
        rw [hfa, hf_ne b hb] at hab
        exact absurd hab.symm (e ⟨b, hb⟩).property
    · by_cases hb : b = x
      · have hfb : f b = y := by rw [hb, hf_x]
        rw [hf_ne a ha, hfb] at hab
        exact absurd hab (e ⟨a, ha⟩).property
      · rw [hf_ne a ha, hf_ne b hb] at hab
        have hsub := e.injective (Subtype.ext hab)
        exact congrArg Subtype.val hsub
  have hsurj : Function.Surjective f := by
    intro q
    by_cases hq : q = y
    · exact ⟨x, by rw [hf_x, hq]⟩
    · obtain ⟨p, hp⟩ := e.surjective ⟨q, hq⟩
      refine ⟨p.val, ?_⟩
      have hpe : f p.val = e p := by
        rw [hf_ne p.val p.property]
      rw [hpe, hp]
  have hord : ∀ a b : P, f a ≤ f b ↔ a ≤ b := by
    intro a b
    by_cases ha : a = x
    · by_cases hb : b = x
      · rw [ha, hb, hf_x]
        exact ⟨fun _ => le_refl x, fun _ => le_refl y⟩
      · rw [ha, hf_x, hf_ne b hb, hyle]
        have hne : ¬ (y = e ⟨b, hb⟩) := fun h => (e ⟨b, hb⟩).property h.symm
        have hxb : ¬ (x ≤ b) := by rw [hxle]; exact fun h => hb h.symm
        exact iff_of_false hne hxb
    · by_cases hb : b = x
      · rw [hb, hf_ne a ha, hf_x, hyge]
        have hne : ¬ (e ⟨a, ha⟩ = y) := (e ⟨a, ha⟩).property
        have hax : ¬ (a ≤ x) := by rw [hxge]; exact ha
        exact iff_of_false hne hax
      · rw [hf_ne a ha, hf_ne b hb, Subtype.coe_le_coe, e.le_iff_le, Subtype.mk_le_mk]
  refine ⟨RelIso.mk (Equiv.ofBijective f ⟨hinj, hsurj⟩) (fun {a b} => ?_)⟩
  change f a ≤ f b ↔ a ≤ b
  exact hord a b
