import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesProductFiberTransfer
import AFTD.Kb.NumberTheory.GoodSlopesFiber35ColoredGap
import AFTD.Kb.NumberTheory.GoodSlopesFiber35UnitGap
import AFTD.Kb.NumberTheory.GoodSlopesProductFiberSet
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.Tcs.F

/-!
# good_slopes_two_row_fiber_rigidity

Topic: elementary_number_theory   Node: 538772b2ae7e

Provenance: helper lemma. CRT fiber reduction for OP-1027; the fiber bounds are formalized from prior experiments and direction arguments.

Let X be a finite set of 105 elements with input and output coordinate functions over Z/3 and Z/35, and assume the pair of input coordinates is injective. Fix two first-coordinate slopes. If the total number of unit slopes b modulo 35 for which x maps injectively to (y3(x)+a*x3(x), y35(x)+b*x35(x)), summed over the two fixed choices of a, exceeds 40, then every unit slope b gives an injective map for each choice of a.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Finset

-- A complete second slice colors every fiber of the first slice.
private theorem gap105_colored_fiber_transfer {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (x3 y3 : X → ZMod 3) (x35 y35 : X → ZMod 35) (a a' : ZMod 3) (b₀ : ZMod 35)
    (hcard : Fintype.card X = 3 * 35)
    (hx : Function.Injective (fun x => (x3 x, x35 x)))
    (hanchor : Function.Bijective (fun x => (y3 x + a*x3 x, y35 x + b₀*x35 x)))
    (hcomplete : ∀ b : ZMod 35, IsUnit b → Function.Injective (fun x => (y3 x + a'*x3 x, y35 x + b*x35 x)))
    (t : ZMod 3)
    (hbad : ∃ b : ZMod 35, IsUnit b ∧ ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + b*p.1)
      (good_slopes_product_fiber_set x3 y3 x35 y35 a t)) :
    (good_slopes_point_directions 35 (good_slopes_product_fiber_set x3 y3 x35 y35 a t)).card ≤ 16 := by
  classical
  let S := good_slopes_product_fiber_set x3 y3 x35 y35 a t
  let F : Finset X := univ.filter fun x => y3 x + a*x3 x = t
  let Q : X → ZMod 35 × ZMod 35 := fun x => (x35 x, y35 x)
  have hs : S = F.image Q := by rfl
  have hxrep (p : ZMod 35 × ZMod 35) (hp : p ∈ S) : ∃ x ∈ F, Q x = p := by
    rw [hs, mem_image] at hp
    exact hp
  let rep : (ZMod 35 × ZMod 35) → X := fun p =>
    if h : ∃ x ∈ F, Q x = p then Classical.choose h else Classical.choice inferInstance
  have hrep (p : ZMod 35 × ZMod 35) (hp : p ∈ S) : rep p ∈ F ∧ Q (rep p) = p := by
    have hex := hxrep p hp
    simp only [rep, dif_pos hex]
    exact Classical.choose_spec hex
  let color : (ZMod 35 × ZMod 35) → Fin 3 := fun p => ⟨(x3 (rep p)).val, ZMod.val_lt _⟩
  have hc (p q : ZMod 35 × ZMod 35) (hpq : color p = color q) : x3 (rep p) = x3 (rep q) := by
    apply ZMod.val_injective
    exact congrArg Fin.val hpq
  have hct : S.card = 35 := by
    have h := (good_slopes_product_fiber_transfer x3 y3 x35 y35 a b₀ (by simpa using hcard) hanchor).1 t
    simpa [S] using h
  apply good_slopes_fiber35_colored_gap S color hct
  · intro p hp q hq hpq hfst
    have ep := hrep p hp
    have eq := hrep q hq
    have hx3 := hc p q hpq
    have hx35 : x35 (rep p) = x35 (rep q) := by
      calc
        x35 (rep p) = p.1 := congrArg Prod.fst ep.2
        _ = q.1 := hfst
        _ = x35 (rep q) := (congrArg Prod.fst eq.2).symm
    have he : rep p = rep q := hx (Prod.ext hx3 hx35)
    rw [← ep.2, ← eq.2, he]
  · intro b hb p hp q hq hpq heq
    have ep := hrep p hp
    have eq := hrep q hq
    have hx3 := hc p q hpq
    have hp3 := (mem_filter.mp ep.1).2
    have hq3 := (mem_filter.mp eq.1).2
    have hy3 : y3 (rep p) = y3 (rep q) := by rw [hx3] at hp3; linear_combination hp3 - hq3
    have he : rep p = rep q := hcomplete b hb (Prod.ext (by dsimp; rw [hx3,hy3]) (by
      dsimp
      have ep1 : x35 (rep p) = p.1 := congrArg Prod.fst ep.2
      have ep2 : y35 (rep p) = p.2 := congrArg Prod.snd ep.2
      have eq1 : x35 (rep q) = q.1 := congrArg Prod.fst eq.2
      have eq2 : y35 (rep q) = q.2 := congrArg Prod.snd eq.2
      rw [ep1, ep2, eq1, eq2]
      exact heq))
    rw [← ep.2, ← eq.2, he]
  · obtain ⟨b, hb, hn⟩ := hbad
    refine ⟨b, hb, ?_⟩
    intro hm
    apply hn
    unfold good_slopes_point_directions at hm
    exact (mem_filter.mp hm).2.2

private theorem gap105_colored_row_transfer {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (x3 y3 : X → ZMod 3) (x35 y35 : X → ZMod 35) (a a' : ZMod 3) (b₀ : ZMod 35)
    (hcard : Fintype.card X = 3 * 35)
    (hx : Function.Injective (fun x => (x3 x, x35 x)))
    (hanchor : Function.Bijective (fun x => (y3 x + a*x3 x, y35 x + b₀*x35 x)))
    (hcomplete : ∀ b : ZMod 35, IsUnit b → Function.Injective (fun x => (y3 x + a'*x3 x, y35 x + b*x35 x)))
    (hbad : ∃ b : ZMod 35, IsUnit b ∧ ¬ Function.Injective (fun x => (y3 x + a*x3 x, y35 x + b*x35 x))) :
    (univ.filter fun b : ZMod 35 => IsUnit b ∧ Function.Injective (fun x => (y3 x + a*x3 x, y35 x + b*x35 x))).card ≤ 16 := by
  classical
  obtain ⟨b, hb, hbad⟩ := hbad
  have ht : ∃ t : ZMod 3, ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + b*p.1)
      (good_slopes_product_fiber_set x3 y3 x35 y35 a t) := by
    by_contra hn
    apply hbad
    apply (good_slopes_product_fiber_transfer x3 y3 x35 y35 a b₀ (by simpa using hcard) hanchor).2.2 b
    simpa only [not_exists, not_not] using hn
  obtain ⟨t, ht⟩ := ht
  have hcount := gap105_colored_fiber_transfer x3 y3 x35 y35 a a' b₀ hcard hx hanchor hcomplete t ⟨b, hb, ht⟩
  apply le_trans (Finset.card_le_card ?_) hcount
  intro b' hb'
  simp only [mem_filter, mem_univ, true_and] at hb'
  unfold good_slopes_point_directions
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hb'.1, (good_slopes_product_fiber_transfer x3 y3 x35 y35 a b₀ (by simpa using hcard) hanchor).2.1 t b' hb'.2⟩

private theorem gap105_uncolored_row_transfer {X : Type*} [Fintype X] [DecidableEq X]
    (x3 y3 : X → ZMod 3) (x35 y35 : X → ZMod 35) (a : ZMod 3) (b₀ : ZMod 35)
    (hcard : Fintype.card X = 3 * 35)
    (hanchor : Function.Bijective (fun x => (y3 x + a*x3 x, y35 x + b₀*x35 x)))
    (hbad : ∃ b : ZMod 35, IsUnit b ∧ ¬ Function.Injective (fun x => (y3 x + a*x3 x, y35 x + b*x35 x))) :
    (univ.filter fun b : ZMod 35 => IsUnit b ∧ Function.Injective (fun x => (y3 x + a*x3 x, y35 x + b*x35 x))).card ≤ 20 := by
  classical
  obtain ⟨b, hb, hbad⟩ := hbad
  have ht : ∃ t : ZMod 3, ¬ Set.InjOn (fun p : ZMod 35 × ZMod 35 => p.2 + b*p.1)
      (good_slopes_product_fiber_set x3 y3 x35 y35 a t) := by
    by_contra hn
    apply hbad
    apply (good_slopes_product_fiber_transfer x3 y3 x35 y35 a b₀ (by simpa using hcard) hanchor).2.2 b
    simpa only [not_exists, not_not] using hn
  obtain ⟨t, ht⟩ := ht
  have hct : (good_slopes_product_fiber_set x3 y3 x35 y35 a t).card = 35 := by
    have h := (good_slopes_product_fiber_transfer x3 y3 x35 y35 a b₀ (by simpa using hcard) hanchor).1 t
    simpa using h
  have hlocal : b ∉ good_slopes_point_directions 35 (good_slopes_product_fiber_set x3 y3 x35 y35 a t) := by
    intro hm
    apply ht
    unfold good_slopes_point_directions at hm
    exact (mem_filter.mp hm).2.2
  have hcount := good_slopes_fiber35_unit_gap _ hct ⟨b, hb, hlocal⟩
  apply le_trans (Finset.card_le_card ?_) hcount
  intro b' hb'
  simp only [mem_filter, mem_univ, true_and] at hb'
  unfold good_slopes_point_directions
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hb'.1, (good_slopes_product_fiber_transfer x3 y3 x35 y35 a b₀ (by simpa using hcard) hanchor).2.1 t b' hb'.2⟩

theorem good_slopes_two_row_fiber_rigidity {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (x3 y3 : X → ZMod 3) (x35 y35 : X → ZMod 35) (a a' : ZMod 3)
    (hcard : Fintype.card X = 3 * 35)
    (hx : Function.Injective (fun x => (x3 x, x35 x)))
    (hlarge : (univ.filter fun b : ZMod 35 => IsUnit b ∧ Function.Injective (fun x => (y3 x + a*x3 x, y35 x + b*x35 x))).card +
      (univ.filter fun b : ZMod 35 => IsUnit b ∧ Function.Injective (fun x => (y3 x + a'*x3 x, y35 x + b*x35 x))).card > 40) :
    (∀ b : ZMod 35, IsUnit b → Function.Injective (fun x => (y3 x + a*x3 x, y35 x + b*x35 x))) ∧
    (∀ b : ZMod 35, IsUnit b → Function.Injective (fun x => (y3 x + a'*x3 x, y35 x + b*x35 x))) := by
  classical
  let R : ZMod 3 → Finset (ZMod 35) := fun q => univ.filter fun b => IsUnit b ∧ Function.Injective (fun x => (y3 x + q*x3 x, y35 x + b*x35 x))
  have hlarge' : 40 < (R a).card + (R a').card := hlarge
  have hbound (q : ZMod 3) : (R q).card ≤ 24 := by
    have hsub : R q ⊆ univ.filter (fun b : ZMod 35 => IsUnit b) := by
      intro b hb
      simp only [R, mem_filter, mem_univ, true_and] at hb ⊢
      exact hb.1
    have h := Finset.card_le_card hsub
    have hc : (univ.filter (fun b : ZMod 35 => IsUnit b)).card = 24 := by decide
    omega
  have ha : 0 < (R a).card := by have := hbound a'; omega
  have ha' : 0 < (R a').card := by have := hbound a; omega
  have anchor (q : ZMod 3) (h : 0 < (R q).card) : ∃ b : ZMod 35,
      Function.Bijective (fun x => (y3 x + q*x3 x, y35 x + b*x35 x)) := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp h
    simp only [R, mem_filter, mem_univ, true_and] at hb
    refine ⟨b, (Fintype.bijective_iff_injective_and_card _).2 ⟨hb.2, ?_⟩⟩
    simpa using hcard
  obtain ⟨b0, hb0⟩ := anchor a ha
  obtain ⟨b1, hb1⟩ := anchor a' ha'
  have key (q q' : ZMod 3) (c0 c1 : ZMod 35)
      (hc0 : Function.Bijective (fun x => (y3 x + q*x3 x, y35 x + c0*x35 x)))
      (hc1 : Function.Bijective (fun x => (y3 x + q'*x3 x, y35 x + c1*x35 x)))
      (hl : 40 < (R q).card + (R q').card) :
      ∀ b : ZMod 35, IsUnit b → Function.Injective (fun x => (y3 x + q*x3 x, y35 x + b*x35 x)) := by
    intro b hb
    by_contra hbad
    have h20 : (R q).card ≤ 20 :=
      gap105_uncolored_row_transfer x3 y3 x35 y35 q c0 hcard hc0 ⟨b, hb, hbad⟩
    have hfull : ∀ d : ZMod 35, IsUnit d → Function.Injective (fun x => (y3 x + q'*x3 x, y35 x + d*x35 x)) := by
      intro d hd
      by_contra hbad'
      have h20' : (R q').card ≤ 20 :=
        gap105_uncolored_row_transfer x3 y3 x35 y35 q' c1 hcard hc1 ⟨d, hd, hbad'⟩
      omega
    have h16 : (R q).card ≤ 16 :=
      gap105_colored_row_transfer x3 y3 x35 y35 q q' c0 hcard hx hc0 hfull ⟨b, hb, hbad⟩
    have := hbound q'
    omega
  exact ⟨key a a' b0 b1 hb0 hb1 hlarge', key a' a b1 b0 hb1 hb0 (by omega)⟩
