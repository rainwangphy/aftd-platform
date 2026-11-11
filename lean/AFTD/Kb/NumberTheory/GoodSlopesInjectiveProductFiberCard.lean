import AFTD.Prelude

/-!
# good_slopes_injective_product_fiber_card

Topic: elementary_number_theory   Node: 1aba438c58d4

Provenance: helper lemma. Finite-fiber counting for the CRT reduction in the 35-point fiber route to OP-1027.

If an injective map on a finite set of size |Y| times |Z| takes values in Y times Z, then each fiber of its first coordinate has |Z| elements.
-/

theorem good_slopes_injective_product_fiber_card {X Y Z : Type*} [DecidableEq X] [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z] (S : Finset X) (f : X → Y × Z) (hinj : Set.InjOn f S) (hcard : S.card = Fintype.card Y * Fintype.card Z) (y : Y) : (S.filter fun x => (f x).1 = y).card = Fintype.card Z := by
  classical
  have hfull : S.image f = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_prod]
  have htarget : (S.filter fun x => (f x).1 = y).image f = {y} ×ˢ Finset.univ := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨x, ⟨hx,hxy⟩, rfl⟩
      exact hxy
    · intro hz
      have hzfull : z ∈ S.image f := by rw [hfull]; exact Finset.mem_univ z
      obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hzfull
      refine ⟨x, ⟨hx, ?_⟩, hxz⟩
      rw [hxz]
      exact hz
  have hfi : Set.InjOn f (S.filter fun x => (f x).1 = y) := by
    intro a ha b hb hab
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  rw [← Finset.card_image_of_injOn hfi, htarget]
  simp
