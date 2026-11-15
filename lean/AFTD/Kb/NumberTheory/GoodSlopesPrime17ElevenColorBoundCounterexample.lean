import AFTD.Prelude

/-!
# good_slopes_prime17_eleven_color_bound_counterexample

Topic: elementary_number_theory   Node: 1c00080d247e

Provenance: helper lemma. Counterexample identified in computation 27605 for the OP-1027 fiber investigation.

There are seventeen graph points over Z/17 with nine ordinate values, seven good nonzero directions, and a collision at direction 2. Coloring points by their ordinate uses nine of eleven available colors and is injective within each color on every nonzero-direction form, refuting the proposed six-direction bound.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 15000

theorem good_slopes_prime17_eleven_color_bound_counterexample :
    ∃ (S : Finset (ZMod 17 × ZMod 17)) (color : (ZMod 17 × ZMod 17) → Fin 11),
      S.card = 17 ∧ (S.image fun p => p.2).card = 9 ∧
      (∀ p ∈ S, ∀ q ∈ S, color p = color q → p.1 = q.1 → p = q) ∧
      (∀ b : ZMod 17, IsUnit b → ∀ p ∈ S, ∀ q ∈ S, color p = color q →
        p.2+b*p.1 = q.2+b*q.1 → p = q) ∧
      7 ≤ ((Finset.univ : Finset (ZMod 17)).filter fun a => IsUnit a ∧
        Set.InjOn (fun p : ZMod 17 × ZMod 17 => p.2 + a*p.1) S).card ∧
      IsUnit (2 : ZMod 17) ∧
      ¬ Set.InjOn (fun p : ZMod 17 × ZMod 17 => p.2 + 2*p.1) S := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  let S : Finset (ZMod 17 × ZMod 17) := {
    (0,0), (1,9), (2,9), (3,10), (4,4), (5,10), (6,16), (7,12), (8,4),
    (9,0), (10,6), (11,12), (12,6), (13,7), (14,7), (15,16), (16,8)}
  let color : (ZMod 17 × ZMod 17) → Fin 11 := fun p => ⟨p.2.val % 11, Nat.mod_lt _ (by decide)⟩
  let Y : Finset (ZMod 17) := {0,4,6,7,8,9,10,12,16}
  have hY : S.image Prod.snd ⊆ Y := by decide
  have htable : ∀ y ∈ Y, ∀ z ∈ Y, y.val % 11 = z.val % 11 → y = z := by decide
  have hsame : ∀ p ∈ S, ∀ q ∈ S, color p = color q → p.2 = q.2 := by
    intro p hp q hq hc
    apply htable p.2 (hY (Finset.mem_image.mpr ⟨p,hp,rfl⟩)) q.2 (hY (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
    exact congrArg Fin.val hc
  have hcardx : (S.image fun p => p.1).card = S.card := by decide
  have hxin : Set.InjOn (fun p : ZMod 17 × ZMod 17 => p.1) S := Finset.card_image_iff.mp hcardx
  let allowed17 : Finset (ZMod 17) := {1,5,7,9,10,12,14}
  have hG : allowed17.card = 7 := by decide
  have hunit : ∀ a ∈ allowed17, IsUnit a := by decide
  have hgood : ∀ a ∈ allowed17, (S.image fun p => p.2 + a*p.1).card = 17 := by
    intro a ha
    simp only [allowed17, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  refine ⟨S, color, by decide, by decide, ?_, ?_, ?_, by decide, ?_⟩
  · intro p hp q hq _ heq
    exact hxin hp hq heq
  · intro b hb p hp q hq hc heq
    have hy := hsame p hp q hq hc
    have hmul : b * (p.1-q.1) = 0 := by linear_combination heq - hy
    have hb0 : b ≠ 0 := hb.ne_zero
    have hx : p.1 = q.1 := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hb0)
    exact Prod.ext hx hy
  · have hsub : allowed17 ⊆ (Finset.univ : Finset (ZMod 17)).filter (fun a => IsUnit a ∧
        Set.InjOn (fun p : ZMod 17 × ZMod 17 => p.2 + a*p.1) S) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hunit a ha, Finset.card_image_iff.mp ?_⟩
      rw [hgood a ha]
      decide
    have h := Finset.card_le_card hsub
    omega
  · intro hinj
    have hp : (0,0) ∈ S := by decide
    have hq : (11,12) ∈ S := by decide
    have hcollision : (0 : ZMod 17) + 2*0 = 12 + 2*11 := by decide
    exact (by decide : ((0,0) : ZMod 17 × ZMod 17) ≠ (11,12)) (hinj hp hq hcollision)
