import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPrime11ThreeAnchor
import AFTD.Kb.GoodSlopesAffineCoordinatesForm
import AFTD.Kb.GoodSlopesAffineCoordinatesAnchors
import AFTD.Kb.GoodSlopesAffineSlopeFractionalInjective
import AFTD.Kb.GoodSlopesAffineCoordinates

/-!
# good_slopes_prime11_six_good_lines

Topic: elementary_number_theory   Node: d3f9b47a1ffd

Provenance: helper lemma. arXiv:2611.04551 Lemma 2.7(ii), specialized to the prime 11.

Any eleven-point set in the affine plane over the field of eleven elements with six good finite directions is a line.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
private theorem in962_nonzero11 (a : ZMod 11) :
    a ≠ 0 → a ∈ ({1,2,3,4,5,6,7,8,9,10} : Finset (ZMod 11)) := by
  revert a
  decide

private theorem in962_card11 :
    ({1,2,3,4,5,6,7,8,9,10} : Finset (ZMod 11)).card = 10 := by decide

private theorem in962_coords_injective {K : Type*} [Field K] (u v w : K × K)
    (hd : (v.1-u.1)*(w.2-u.2)-(w.1-u.1)*(v.2-u.2) ≠ 0) :
    Function.Injective (good_slopes_affine_coordinates u v w) := by
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have hf (a : K) : x.2+a*x.1 = y.2+a*y.1 := by
    rw [good_slopes_affine_coordinates_form u v w x a hd,
      good_slopes_affine_coordinates_form u v w y a hd, h1, h2]
  have h0 := hf 0
  have h1' := hf 1
  apply Prod.ext
  · linear_combination h1' - h0
  · simpa using h0

private theorem in962_noncollinear {K : Type*} [Field K] [DecidableEq K]
    (S : Finset (K × K)) (hcard : 1 < S.card)
    (hnotv : ¬ ∃ x : K, ∀ p ∈ S, p.1 = x)
    (hnotl : ¬ ∃ a t : K, ∀ p ∈ S, p.2 + a*p.1 = t) :
    ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S,
      (v.1-u.1)*(w.2-u.2)-(w.1-u.1)*(v.2-u.2) ≠ 0 := by
  classical
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hcard
  by_contra hex
  push Not at hex
  by_cases hx : v.1-u.1 = 0
  · have hy : v.2-u.2 ≠ 0 := by
      intro h
      apply huv
      exact Prod.ext (sub_eq_zero.mp hx).symm (sub_eq_zero.mp h).symm
    apply hnotv
    refine ⟨u.1, ?_⟩
    intro w hw
    have hw0 := hex u hu v hv w hw
    have hwx : (w.1-u.1)*(v.2-u.2) = 0 := by linear_combination -hw0 + (w.2-u.2)*hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hwx).resolve_right hy)
  · apply hnotl
    refine ⟨-(v.2-u.2)/(v.1-u.1), u.2 + (-(v.2-u.2)/(v.1-u.1))*u.1, ?_⟩
    intro w hw
    have hw0 := hex u hu v hv w hw
    apply (mul_right_inj' hx).mp
    field_simp
    linear_combination hw0

theorem good_slopes_prime11_six_good_lines (S : Finset (ZMod 11 × ZMod 11)) (G : Finset (ZMod 11)) (hcard : S.card = 11) (hgood : 6 ≤ G.card) (hinj : ∀ a ∈ G, Set.InjOn (fun p : ZMod 11 × ZMod 11 => p.2 + a*p.1) S) : (∃ x : ZMod 11, ∀ p ∈ S, p.1 = x) ∨ (∃ a t : ZMod 11, ∀ p ∈ S, p.2 + a*p.1 = t) := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  by_contra hnot
  have hnotv : ¬ ∃ x : ZMod 11, ∀ p ∈ S, p.1 = x := fun h => hnot (Or.inl h)
  have hnotl : ¬ ∃ a t : ZMod 11, ∀ p ∈ S, p.2+a*p.1 = t := fun h => hnot (Or.inr h)
  obtain ⟨u,hu,v,hv,w,hw,hd⟩ := in962_noncollinear S (by omega) hnotv hnotl
  let φ := good_slopes_affine_coordinates u v w
  have hφ : Function.Injective φ := in962_coords_injective u v w hd
  let S' := S.image φ
  have hS' : S'.card = 11 := by
    dsimp [S']
    rw [Finset.card_image_of_injective _ hφ, hcard]
  obtain ⟨h0,h1,h2⟩ := good_slopes_affine_coordinates_anchors u v w hd
  have hu' : ((0 : ZMod 11), 0) ∈ S' := Finset.mem_image.mpr ⟨u,hu,h0⟩
  have hv' : ((1 : ZMod 11), 0) ∈ S' := Finset.mem_image.mpr ⟨v,hv,h1⟩
  have hw' : ((0 : ZMod 11), 1) ∈ S' := Finset.mem_image.mpr ⟨w,hw,h2⟩
  have huv : u ≠ v := by
    intro he
    subst v
    simp at hd
  have huw : u ≠ w := by
    intro he
    subst w
    simp at hd
  let α (a : ZMod 11) := v.2-u.2+a*(v.1-u.1)
  let β (a : ZMod 11) := w.2-u.2+a*(w.1-u.1)
  have hα (a : ZMod 11) (ha : a ∈ G) : α a ≠ 0 := by
    intro hz
    apply huv
    apply hinj a ha hu hv
    dsimp [α] at hz
    linear_combination -hz
  have hβ (a : ZMod 11) (ha : a ∈ G) : β a ≠ 0 := by
    intro hz
    apply huw
    apply hinj a ha hu hw
    dsimp [β] at hz
    linear_combination -hz
  let ψ (a : ZMod 11) := α a / β a
  have hψ : Set.InjOn ψ G := by
    intro a ha b hb heq
    exact good_slopes_affine_slope_fractional_injective
      (v.1-u.1) (v.2-u.2) (w.1-u.1) (w.2-u.2) a b hd
      (hβ a ha) (hβ b hb) heq
  let T : Finset (ZMod 11) := G.image ψ
  have hTcard : 6 ≤ T.card := by
    dsimp [T]
    rw [Finset.card_image_of_injOn hψ]
    exact hgood
  have hTzero : (0 : ZMod 11) ∉ T := by
    intro hz
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hz
    have := (div_eq_zero_iff).mp (by simpa [ψ] using heq)
    exact hα a ha (this.resolve_right (hβ a ha))
  let U : Finset (ZMod 11) := {1,2,3,4,5,6,7,8,9,10}
  have hTsub : T ⊆ U := by
    intro a ha
    have hne : a ≠ 0 := by intro ha0; apply hTzero; simpa [ha0] using ha
    exact in962_nonzero11 a hne
  have hTin : ∀ a ∈ T, Set.InjOn (fun p : ZMod 11 × ZMod 11 => p.2 + a*p.1) S' := by
    intro a ha x hx y hy heq
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x,hx0,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hy0,rfl⟩ := Finset.mem_image.mp hy
    apply congrArg φ
    apply hinj b hb hx0 hy0
    have hxform := good_slopes_affine_coordinates_form u v w x b hd
    have hyform := good_slopes_affine_coordinates_form u v w y b hd
    change x.2+b*x.1 = u.2+b*u.1 + α b*(φ x).1 + β b*(φ x).2 at hxform
    change y.2+b*y.1 = u.2+b*u.1 + α b*(φ y).1 + β b*(φ y).2 at hyform
    change (φ x).2 + (α b / β b)*(φ x).1 = (φ y).2 + (α b / β b)*(φ y).1 at heq
    have hs := congrArg (fun z : ZMod 11 => β b * z) heq
    have hcancel : β b * (α b / β b) = α b := by field_simp [hβ b hb]
    simp only [mul_add, ← mul_assoc, hcancel] at hs
    linear_combination hxform - hyform + hs
  have hcover : ∀ a ∈ U, a ∈ T → ∀ t : ZMod 11, ∃ p ∈ S', p.2 + a*p.1 = t := by
    intro a _ ha t
    have himg : S'.image (fun p : ZMod 11 × ZMod 11 => p.2+a*p.1) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn (hTin a ha), hS', ZMod.card]
    have ht : t ∈ S'.image (fun p : ZMod 11 × ZMod 11 => p.2+a*p.1) := by
      rw [himg]; exact Finset.mem_univ t
    exact Finset.mem_image.mp ht
  have hfive : ∀ A : Finset (ZMod 11), A ⊆ U → A.card = 5 → ∃ a ∈ A, a ∈ T := by
    intro A hAU hAc
    by_contra hn
    push Not at hn
    have hsub : T ⊆ U \ A := by
      intro a ha
      exact Finset.mem_sdiff.mpr ⟨hTsub ha, fun haa => hn a haa ha⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hAU, hAc] at hc
    have : U.card = 10 := in962_card11
    omega
  exact good_slopes_prime11_three_anchor S' (fun a => a ∈ T) hu' hv' hw'
    (fun a _ ha => hTin a ha) hcover hfive
