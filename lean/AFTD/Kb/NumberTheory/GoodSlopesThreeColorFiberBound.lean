import AFTD.Prelude

/-!
# good_slopes_three_color_fiber_bound

Topic: elementary_number_theory   Node: c95c3cec04a8

Provenance: helper lemma. Finite counting and CRT arithmetic in the OP-1027 modulus 105 reduction.

If a function is injective on each of three colors, every fiber contains at most three points.
-/

theorem good_slopes_three_color_fiber_bound {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (S : Finset X) (f : X → Y) (c : X → Fin 3)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, c p = c q → f p = f q → p = q) (t : Y) :
    (S.filter fun p => f p = t).card ≤ 3 := by
  classical
  have hi : Set.InjOn c (S.filter fun p => f p = t) := by
    intro p hp q hq heq
    exact hinj p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 heq
      ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
  calc
    (S.filter fun p => f p = t).card = ((S.filter fun p => f p = t).image c).card :=
      (Finset.card_image_of_injOn hi).symm
    _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 3 := by simp
