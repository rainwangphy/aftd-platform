import AFTD.Prelude
import AFTD.Kb.Tcs.PosetLtPairCount

/-!
# poset_delete_isolated_lt_pair_count_iff

Topic: combinatorics   Node: a9b94082480b

Provenance: helper lemma. step towards poset_height_one_reconstructible

In a finite ordered set, the one-element deletion P − x has the same number of comparable pairs as P if and only if x is incomparable with every other element.
-/

/-- Deleting a point preserves the comparable-pair count exactly when that point is isolated. -/
theorem poset_delete_isolated_lt_pair_count_iff (P : Type) [Fintype P] [PartialOrder P] (x : P) : poset_lt_pair_count {y : P // y ≠ x} = poset_lt_pair_count P ↔ (∀ y : P, ¬ (x < y ∨ y < x)) := by
  classical
  unfold poset_lt_pair_count
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  let f : {p : {y : P // y ≠ x} × {y : P // y ≠ x} // p.1 < p.2} →
          {p : P × P // p.1 < p.2} := fun p => ⟨(p.1.1.1, p.1.2.1), p.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have h := Subtype.ext_iff.mp hpq
    simp only [f] at h
    have h1 : p.1.1 = q.1.1 := Subtype.ext (congrArg Prod.fst h)
    have h2 : p.1.2 = q.1.2 := Subtype.ext (congrArg Prod.snd h)
    exact Subtype.ext (Prod.ext h1 h2)
  constructor
  · -- (equal card) -> isolated
    intro hcard
    have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
    intro y hcon
    rcases hcon with hlt | hlt
    · obtain ⟨p, hp⟩ := hbij.2 ⟨(x, y), hlt⟩
      have h1 : (f p).val.1 ≠ x := by simpa [f] using p.1.1.property
      have : (f p).val.1 = x := by rw [hp]
      exact h1 this
    · obtain ⟨p, hp⟩ := hbij.2 ⟨(y, x), hlt⟩
      have h2 : (f p).val.2 ≠ x := by simpa [f] using p.1.2.property
      have : (f p).val.2 = x := by rw [hp]
      exact h2 this
  · -- isolated -> equal card
    intro hiso
    have hsurj : Function.Surjective f := by
      rintro ⟨⟨a, b⟩, hab⟩
      have ha : a ≠ x := by rintro rfl; exact hiso b (Or.inl hab)
      have hb : b ≠ x := by rintro rfl; exact hiso a (Or.inr hab)
      refine ⟨⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩, ?_⟩
      rfl
    exact Fintype.card_of_bijective ⟨hf, hsurj⟩
