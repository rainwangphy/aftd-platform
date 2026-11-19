import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirectionsCrtTransfer
import AFTD.Kb.Tcs.GoodSlopesProductThreeColorGapConditional
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_colored_product_gap_crt_conditional

Topic: elementary_number_theory   Node: fda99fca8310

Provenance: helper lemma. CRT transfer of the finite-field product bounds for OP-1027.

Under the stated prime, size and finite-field direction hypotheses, a three-colored set of pq points modulo pq with a bad unit direction has at most (p−1)(q−1)−2(p−1) good unit directions, provided the first coordinate and every unit-direction form are injective within each color.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_colored_product_gap_crt_conditional (p q : ℕ) [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    (hcop : Nat.Coprime p q) (hp5 : 5 ≤ p) (hpodd : p % 2 = 1) (hqodd : q % 2 = 1)
    (hsep : 2*p-1 ≤ q) (hsize : (p+1)*3 < 2*q)
    (hdirP : ∀ T : Finset (ZMod p × ZMod p), T.card = p →
      (∃ G : Finset (ZMod p), (p+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : ZMod p × ZMod p => z.2+a*z.1) T) →
      (∃ x : ZMod p, ∀ z ∈ T, z.1=x) ∨ (∃ a t : ZMod p, ∀ z ∈ T, z.2+a*z.1=t))
    (hdirQ : ∀ T : Finset (ZMod q × ZMod q), T.card = q →
      (∃ G : Finset (ZMod q), (q+1)/2 ≤ G.card ∧ ∀ a ∈ G, Set.InjOn (fun z : ZMod q × ZMod q => z.2+a*z.1) T) →
      (∃ x : ZMod q, ∀ z ∈ T, z.1=x) ∨ (∃ a t : ZMod q, ∀ z ∈ T, z.2+a*z.1=t))
    (S : Finset (ZMod (p*q) × ZMod (p*q))) (color : (ZMod (p*q) × ZMod (p*q)) → Fin 3)
    (hcard : S.card = p*q)
    (hx : ∀ u ∈ S, ∀ v ∈ S, color u = color v → u.1 = v.1 → u=v)
    (hc : ∀ b : ZMod (p*q), IsUnit b → ∀ u ∈ S, ∀ v ∈ S, color u = color v → u.2+b*u.1=v.2+b*v.1 → u=v)
    (hbad : ∃ b : ZMod (p*q), IsUnit b ∧ b ∉ good_slopes_point_directions (p*q) S) :
    (good_slopes_point_directions (p*q) S).card ≤ (p-1)*(q-1)-2*(p-1) := by
  classical
  let e := ZMod.chineseRemainder hcop
  let E := Equiv.prodCongr e.toEquiv e.toEquiv
  let S' := S.image E
  let C (z : ((ZMod p × ZMod q) × (ZMod p × ZMod q))) := color (E.symm z)
  have hS' : S'.card = p*q := by
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
  have hci : ∀ a : ZMod p, a ≠ 0 → ∀ b : ZMod q, b ≠ 0 → ∀ u ∈ S', ∀ v ∈ S', C u = C v →
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
  let Good : Finset (ZMod p × ZMod q) := (Finset.univ : Finset (ZMod p × ZMod q)).filter fun ab =>
    ab.1 ≠ 0 ∧ ab.2 ≠ 0 ∧ Set.InjOn (fun z : ((ZMod p × ZMod q) × (ZMod p × ZMod q)) =>
      (z.2.1+ab.1*z.1.1,z.2.2+ab.2*z.1.2)) S'
  have hcrt (c : ZMod (p*q)) : c ∈ good_slopes_point_directions (p*q) S ↔
      (e c).1 ≠ 0 ∧ (e c).2 ≠ 0 ∧ Set.InjOn (fun z : ((ZMod p × ZMod q) × (ZMod p × ZMod q)) =>
        (z.2.1+(e c).1*z.1.1,z.2.2+(e c).2*z.1.2)) S' :=
    good_slopes_point_directions_crt_transfer p q hcop S c
  have hGood : Good = (good_slopes_point_directions (p*q) S).image e := by
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
  have hbad' : ∃ a : ZMod p, a ≠ 0 ∧ ∃ b : ZMod q, b ≠ 0 ∧
      ¬ Set.InjOn (fun z : ((ZMod p × ZMod q) × (ZMod p × ZMod q)) =>
        (z.2.1+a*z.1.1,z.2.2+b*z.1.2)) S' := by
    obtain ⟨c,hcu,hcbad⟩ := hbad
    have hu : IsUnit (e c) := (MulEquiv.isUnit_map e).mpr hcu
    have ⟨hu5,hu11⟩ := Prod.isUnit_iff.mp hu
    refine ⟨(e c).1,isUnit_iff_ne_zero.mp hu5,(e c).2,isUnit_iff_ne_zero.mp hu11, ?_⟩
    intro hh
    exact hcbad ((hcrt c).mpr ⟨isUnit_iff_ne_zero.mp hu5,isUnit_iff_ne_zero.mp hu11,hh⟩)
  have h := good_slopes_product_three_color_gap_conditional (ZMod p) (ZMod q) p q
    (by simp) (by simp) hp5 hpodd hqodd hsep hsize hdirP hdirQ S' C hS' hxi hci hbad'
  change Good.card ≤ (p-1)*(q-1)-2*(p-1) at h
  rw [hGood, Finset.card_image_of_injective _ e.injective] at h
  exact h
