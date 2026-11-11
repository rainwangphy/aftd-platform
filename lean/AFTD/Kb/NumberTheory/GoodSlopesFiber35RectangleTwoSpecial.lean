import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesFiber35Rect2

/-!
# good_slopes_fiber35_rectangle_two_special

Topic: elementary_number_theory   Node: ad1045d168ee

Provenance: helper lemma. An exact integer certificate with two triangle inequalities for good_slopes_fiber35_colored_gap, experiment 22293.

No 35-point set containing (0,0) and (1,34) has all unit directions good outside the two-by-three residue rectangle {1,2} modulo 5 by {1,2,4} modulo 7.
-/

theorem good_slopes_fiber35_rectangle_two_special (S : Finset (ZMod 35 × ZMod 35)) (hcard : S.card = 35) (h0 : (0,0) ∈ S) (h1 : (1,34) ∈ S) (hgood : ∀ a : ZMod 35, IsUnit a → ¬ ((a.val % 5 = 1 ∨ a.val % 5 = 2) ∧ (a.val % 7 = 1 ∨ a.val % 7 = 2 ∨ a.val % 7 = 4)) → a ∈ good_slopes_point_directions 35 S) : False := by
  classical
  let G : Finset (ZMod 35) := {3,4,6,8,9,12,13,17,18,19,23,24,26,27,29,31,33,34}
  have htable : ∀ a : ZMod 35, a ∈ G → Nat.Coprime a.val 35 ∧
      ¬ ((a.val % 5 = 1 ∨ a.val % 5 = 2) ∧
        (a.val % 7 = 1 ∨ a.val % 7 = 2 ∨ a.val % 7 = 4)) := by
    dsimp [G]
    decide
  have hinj : ∀ a ∈ G, Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+a*p.1) S := by
    intro a ha
    obtain ⟨hcop, hout⟩ := htable a ha
    have hu : IsUnit a := by
      rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
      exact hcop
    have hg := hgood a hu hout
    have hg' : IsUnit a ∧ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2+a*p.1) S := by
      simpa [good_slopes_point_directions] using hg
    exact hg'.2
  have hcover : ∀ a ∈ G, ∀ t : ZMod 35, ∃ p ∈ S, p.2+a*p.1=t := by
    intro a ha t
    have hi : (S.image (fun p : ZMod 35 × ZMod 35 => p.2+a*p.1)).card = 35 := by
      rw [Finset.card_image_of_injOn (hinj a ha),hcard]
    have hall : S.image (fun p : ZMod 35 × ZMod 35 => p.2+a*p.1) = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hi
    have ht : t ∈ S.image (fun p : ZMod 35 × ZMod 35 => p.2+a*p.1) := by
      rw [hall]; exact Finset.mem_univ t
    exact Finset.mem_image.mp ht
  exact good_slopes_fiber35_rect2 S h0 h1 hinj hcover
