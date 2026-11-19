import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.Tcs.GoodSlopesProductThreeColorGapConditional
import AFTD.Kb.NumberTheory.GoodSlopesPointDirectionsCrtTransfer
import AFTD.Kb.NumberTheory.GoodSlopesPrime11SixGoodLines
import AFTD.Kb.NumberTheory.GoodSlopesPrime5ThreeGoodLines

/-!
# good_slopes_fiber55_colored_gap_structural

Topic: elementary_number_theory   Node: 839568881ec3

Provenance: helper lemma. Colored local fiber bound for OP-1027, from the prime-field direction and three-row arguments.

A three-colored 55-point set over Z/55 with any bad unit direction has at most 32 good unit directions.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_fiber55_colored_gap_structural (S : Finset (ZMod 55 × ZMod 55)) (color : (ZMod 55 × ZMod 55) → Fin 3) (hcard : S.card = 55) (hx : ∀ p ∈ S, ∀ q ∈ S, color p = color q → p.1 = q.1 → p = q) (hc : ∀ b : ZMod 55, IsUnit b → ∀ p ∈ S, ∀ q ∈ S, color p = color q → p.2 + b*p.1 = q.2 + b*q.1 → p = q) (hbad : ∃ b : ZMod 55, IsUnit b ∧ b ∉ good_slopes_point_directions 55 S) : (good_slopes_point_directions 55 S).card ≤ 32 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hcop : Nat.Coprime 5 11 := by decide
  let e := ZMod.chineseRemainder hcop
  let E := Equiv.prodCongr e.toEquiv e.toEquiv
  let S' := S.image E
  let C (z : ((ZMod 5 × ZMod 11) × (ZMod 5 × ZMod 11))) := color (E.symm z)
  have hS' : S'.card = 5*11 := by
    dsimp [S']
    rw [Finset.card_image_of_injective _ E.injective, hcard]
  have hxi : ∀ u ∈ S', ∀ v ∈ S', C u = C v → u.1 = v.1 → u = v := by
    intro u hu v hv hcol heq
    obtain ⟨x,hx0,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy0,rfl⟩ := Finset.mem_image.mp hv
    apply congrArg E
    apply hx x hx0 y hy0
    · simpa [C] using hcol
    · apply e.injective
      exact heq
  have hci : ∀ a : ZMod 5, a ≠ 0 → ∀ b : ZMod 11, b ≠ 0 → ∀ u ∈ S', ∀ v ∈ S', C u = C v →
      (u.2.1+a*u.1.1,u.2.2+b*u.1.2) = (v.2.1+a*v.1.1,v.2.2+b*v.1.2) → u=v := by
    intro a ha b hb u hu v hv hcol heq
    obtain ⟨x,hx0,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy0,rfl⟩ := Finset.mem_image.mp hv
    let d := e.symm (a,b)
    have hd : IsUnit d := by
      apply (MulEquiv.isUnit_map e).mp
      rw [e.apply_symm_apply]
      exact Prod.isUnit_iff.mpr ⟨isUnit_iff_ne_zero.mpr ha,isUnit_iff_ne_zero.mpr hb⟩
    apply congrArg E
    apply hc d hd x hx0 y hy0
    · simpa [C] using hcol
    · apply e.injective
      rw [map_add,map_mul,e.apply_symm_apply,map_add,map_mul,e.apply_symm_apply]
      exact heq
  let Good : Finset (ZMod 5 × ZMod 11) := (Finset.univ : Finset (ZMod 5 × ZMod 11)).filter fun ab =>
    ab.1 ≠ 0 ∧ ab.2 ≠ 0 ∧ Set.InjOn (fun z : ((ZMod 5 × ZMod 11) × (ZMod 5 × ZMod 11)) =>
      (z.2.1+ab.1*z.1.1,z.2.2+ab.2*z.1.2)) S'
  have hcrt (c : ZMod 55) : c ∈ good_slopes_point_directions 55 S ↔
      (e c).1 ≠ 0 ∧ (e c).2 ≠ 0 ∧ Set.InjOn (fun z : ((ZMod 5 × ZMod 11) × (ZMod 5 × ZMod 11)) =>
        (z.2.1+(e c).1*z.1.1,z.2.2+(e c).2*z.1.2)) S' :=
    good_slopes_point_directions_crt_transfer 5 11 hcop S c
  have hGood : Good = (good_slopes_point_directions 55 S).image e := by
    ext ab
    constructor
    · intro hab
      have hh := (Finset.mem_filter.mp hab).2
      refine Finset.mem_image.mpr ⟨e.symm ab, ?_,e.apply_symm_apply ab⟩
      apply (hcrt (e.symm ab)).mpr
      simpa only [e.apply_symm_apply] using hh
    · intro hab
      obtain ⟨c,hc0,rfl⟩ := Finset.mem_image.mp hab
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hcrt c).mp hc0⟩
  have hbad' : ∃ a : ZMod 5, a ≠ 0 ∧ ∃ b : ZMod 11, b ≠ 0 ∧
      ¬ Set.InjOn (fun z : ((ZMod 5 × ZMod 11) × (ZMod 5 × ZMod 11)) =>
        (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S' := by
    obtain ⟨c,hcu,hcbad⟩ := hbad
    have hu : IsUnit (e c) := (MulEquiv.isUnit_map e).mpr hcu
    have ⟨hu5,hu11⟩ := Prod.isUnit_iff.mp hu
    refine ⟨(e c).1,isUnit_iff_ne_zero.mp hu5,(e c).2,isUnit_iff_ne_zero.mp hu11, ?_⟩
    intro hh
    exact hcbad ((hcrt c).mpr ⟨isUnit_iff_ne_zero.mp hu5,isUnit_iff_ne_zero.mp hu11,hh⟩)
  have hdir5 : ∀ T : Finset (ZMod 5 × ZMod 5), T.card = 5 →
      (∃ G : Finset (ZMod 5), (5+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : ZMod 5 × ZMod 5 => z.2+b*z.1) T) →
      (∃ x : ZMod 5, ∀ z ∈ T, z.1=x) ∨ (∃ b t : ZMod 5, ∀ z ∈ T, z.2+b*z.1=t) := by
    intro T ht hG
    obtain ⟨G,hG,hgood⟩ := hG
    exact good_slopes_prime5_three_good_lines T G ht hG hgood
  have hdir11 : ∀ T : Finset (ZMod 11 × ZMod 11), T.card = 11 →
      (∃ G : Finset (ZMod 11), (11+1)/2 ≤ G.card ∧ ∀ b ∈ G, Set.InjOn (fun z : ZMod 11 × ZMod 11 => z.2+b*z.1) T) →
      (∃ x : ZMod 11, ∀ z ∈ T, z.1=x) ∨ (∃ b t : ZMod 11, ∀ z ∈ T, z.2+b*z.1=t) := by
    intro T ht hG
    obtain ⟨G,hG,hgood⟩ := hG
    exact good_slopes_prime11_six_good_lines T G ht hG hgood
  have h := good_slopes_product_three_color_gap_conditional (ZMod 5) (ZMod 11) 5 11
    (by simp) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
    hdir5 hdir11 S' C hS' hxi hci hbad'
  change Good.card ≤ (5-1)*(11-1)-2*(5-1) at h
  rw [hGood, Finset.card_image_of_injective _ e.injective] at h
  exact h
