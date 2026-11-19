import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPrime5AnchoredLine
import AFTD.Kb.GoodSlopesAffineCoordinatesForm
import AFTD.Kb.GoodSlopesAffineCoordinatesAnchors
import AFTD.Kb.GoodSlopesAffineSlopeFractionalInjective
import AFTD.Kb.GoodSlopesAffineCoordinates

/-!
# good_slopes_prime5_three_good_lines

Topic: elementary_number_theory   Node: aee781689fa2

Provenance: helper lemma. Finite five-point direction classification for OP-1027, derived from the checked anchored certificate.

A set of five points in the plane over the field with five elements is a line if at least three finite directions are injective on it.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
private theorem in962_prime5_card : ({2,3,4} : Finset (ZMod 5)).card = 3 := by decide
private theorem in962_prime5_rem (a : ZMod 5) : a ≠ 0 → a ≠ 1 → a ∈ ({2,3,4} : Finset (ZMod 5)) := by
  revert a
  decide
private theorem in962_prime5_negone : (-1 : ZMod 5) = 4 := by decide

private theorem in9625_coords_injective {K : Type*} [Field K] (u v w : K × K)
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

private theorem in9625_noncollinear {K : Type*} [Field K] [DecidableEq K]
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

theorem good_slopes_prime5_three_good_lines
    (S : Finset (ZMod 5 × ZMod 5)) (G : Finset (ZMod 5))
    (hcard : S.card = 5) (hgood : 3 ≤ G.card)
    (hinj : ∀ a ∈ G, Set.InjOn (fun p : ZMod 5 × ZMod 5 => p.2 + a*p.1) S) :
    (∃ x : ZMod 5, ∀ p ∈ S, p.1 = x) ∨
      (∃ a t : ZMod 5, ∀ p ∈ S, p.2 + a*p.1 = t) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  by_contra hnot
  have hnotv : ¬ ∃ x : ZMod 5, ∀ p ∈ S, p.1 = x := fun h => hnot (Or.inl h)
  have hnotl : ¬ ∃ a t : ZMod 5, ∀ p ∈ S, p.2+a*p.1 = t := fun h => hnot (Or.inr h)
  obtain ⟨u,hu,v,hv,w,hw,hd⟩ := in9625_noncollinear S (by omega) hnotv hnotl
  let φ := good_slopes_affine_coordinates u v w
  have hφ : Function.Injective φ := in9625_coords_injective u v w hd
  let S' := S.image φ
  have hS' : S'.card = 5 := by
    dsimp [S']
    rw [Finset.card_image_of_injective _ hφ, hcard]
  obtain ⟨h0,h1,h2⟩ := good_slopes_affine_coordinates_anchors u v w hd
  have hu' : ((0 : ZMod 5), 0) ∈ S' := Finset.mem_image.mpr ⟨u,hu,h0⟩
  have hv' : ((1 : ZMod 5), 0) ∈ S' := Finset.mem_image.mpr ⟨v,hv,h1⟩
  have hw' : ((0 : ZMod 5), 1) ∈ S' := Finset.mem_image.mpr ⟨w,hw,h2⟩
  have huv : u ≠ v := by
    intro he
    subst v
    simp at hd
  have huw : u ≠ w := by
    intro he
    subst w
    simp at hd
  let α (a : ZMod 5) := v.2-u.2+a*(v.1-u.1)
  let β (a : ZMod 5) := w.2-u.2+a*(w.1-u.1)
  have hα (a : ZMod 5) (ha : a ∈ G) : α a ≠ 0 := by
    intro hz
    apply huv
    apply hinj a ha hu hv
    dsimp [α] at hz
    linear_combination -hz
  have hβ (a : ZMod 5) (ha : a ∈ G) : β a ≠ 0 := by
    intro hz
    apply huw
    apply hinj a ha hu hw
    dsimp [β] at hz
    linear_combination -hz
  let ψ (a : ZMod 5) := α a / β a
  have hψ : Set.InjOn ψ G := by
    intro a ha b hb heq
    exact good_slopes_affine_slope_fractional_injective
      (v.1-u.1) (v.2-u.2) (w.1-u.1) (w.2-u.2) a b hd
      (hβ a ha) (hβ b hb) heq
  let T : Finset (ZMod 5) := G.image ψ
  have hTcard : 3 ≤ T.card := by
    dsimp [T]
    rw [Finset.card_image_of_injOn hψ]
    exact hgood
  have hTzero : (0 : ZMod 5) ∉ T := by
    intro hz
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hz
    have := (div_eq_zero_iff).mp (by simpa [ψ] using heq)
    exact hα a ha (this.resolve_right (hβ a ha))
  have hTin : ∀ a ∈ T, Set.InjOn (fun p : ZMod 5 × ZMod 5 => p.2 + a*p.1) S' := by
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
    have hs := congrArg (fun z : ZMod 5 => β b * z) heq
    have hcancel : β b * (α b / β b) = α b := by field_simp [hβ b hb]
    simp only [mul_add, ← mul_assoc, hcancel] at hs
    linear_combination hxform - hyform + hs
  have hTone : (1 : ZMod 5) ∉ T := by
    intro h
    have he : (((1 : ZMod 5),0) : ZMod 5 × ZMod 5) = (0,1) := hTin 1 h hv' hw' (by norm_num)
    have hh := congrArg Prod.fst he
    norm_num at hh
  have hTsub : T ⊆ ({2,3,4} : Finset (ZMod 5)) := by
    intro a ha
    have ha0 : a ≠ 0 := by intro h; apply hTzero; simpa [h] using ha
    have ha1 : a ≠ 1 := by intro h; apply hTone; simpa [h] using ha
    exact in962_prime5_rem a ha0 ha1
  have hTcard3 : ({2,3,4} : Finset (ZMod 5)).card = 3 := in962_prime5_card
  have hTeq : T = ({2,3,4} : Finset (ZMod 5)) := by
    apply Finset.eq_of_subset_of_card_le hTsub
    omega
  let τ (z : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 := (1-z.1,-z.2)
  have hτ : Function.Injective τ := by
    intro x y h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp [τ] at hx hy
    apply Prod.ext
    · linear_combination -hx
    · linear_combination -hy
  let S'' := S'.image τ
  have hS'' : S''.card = 5 := by
    dsimp [S'']
    rw [Finset.card_image_of_injective _ hτ, hS']
  have h0'' : ((0 : ZMod 5),0) ∈ S'' := by
    apply Finset.mem_image.mpr
    refine ⟨((1 : ZMod 5),0),hv', ?_⟩
    simp [τ, in962_prime5_negone]
  have h1'' : ((1 : ZMod 5),4) ∈ S'' := by
    apply Finset.mem_image.mpr
    refine ⟨((0 : ZMod 5),1),hw', ?_⟩
    simp [τ, in962_prime5_negone]
  have hu'' : ((1 : ZMod 5),0) ∈ S'' := by
    apply Finset.mem_image.mpr
    refine ⟨((0 : ZMod 5),0),hu', ?_⟩
    norm_num [τ]
  have hg'' (c : ZMod 5) (hc : c ∈ T) : Set.InjOn (fun z : ZMod 5 × ZMod 5 => z.2+c*z.1) S'' := by
    intro x hx y hy he
    obtain ⟨x,hx0,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y,hy0,rfl⟩ := Finset.mem_image.mp hy
    apply congrArg τ
    apply hTin c hc hx0 hy0
    dsimp [τ] at he
    linear_combination -he
  have ht2 : (2 : ZMod 5) ∈ T := by rw [hTeq]; norm_num
  have ht3 : (3 : ZMod 5) ∈ T := by rw [hTeq]; norm_num
  have ht4 : (4 : ZMod 5) ∈ T := by rw [hTeq]; norm_num
  have hline := good_slopes_prime5_anchored_line S'' hS'' h0'' h1'' (hg'' 2 ht2) (hg'' 3 ht3) (hg'' 4 ht4)
  have habs := hline ((1 : ZMod 5),0) hu''
  norm_num at habs
