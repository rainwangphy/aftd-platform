import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_point_directions_crt_transfer

Topic: elementary_number_theory   Node: 8248c8ca81c8

Provenance: helper lemma. CRT direction transfer for OP-1027.

For coprime primes, a unit good direction on a point set over the product residue ring is equivalent under the Chinese-remainder map to nonzero component directions whose pair of affine forms is injective on the transported point set.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem good_slopes_point_directions_crt_transfer
    (p q : ℕ) [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (hcop : Nat.Coprime p q)
    (S : Finset (ZMod (p*q) × ZMod (p*q))) (c : ZMod (p*q)) :
    let e := ZMod.chineseRemainder hcop
    let E := Equiv.prodCongr e.toEquiv e.toEquiv
    c ∈ good_slopes_point_directions (p*q) S ↔
      (e c).1 ≠ 0 ∧ (e c).2 ≠ 0 ∧
      Set.InjOn (fun z : ((ZMod p × ZMod q) × (ZMod p × ZMod q)) =>
        (z.2.1+(e c).1*z.1.1,z.2.2+(e c).2*z.1.2)) (S.image E) := by
  classical
  let e := ZMod.chineseRemainder hcop
  let E := Equiv.prodCongr e.toEquiv e.toEquiv
  let F (z : ((ZMod p × ZMod q) × (ZMod p × ZMod q))) :=
    (z.2.1+(e c).1*z.1.1,z.2.2+(e c).2*z.1.2)
  change c ∈ good_slopes_point_directions (p*q) S ↔
    (e c).1 ≠ 0 ∧ (e c).2 ≠ 0 ∧ Set.InjOn F (S.image E)
  have hunit : IsUnit c ↔ (e c).1 ≠ 0 ∧ (e c).2 ≠ 0 := by
    rw [← MulEquiv.isUnit_map e, Prod.isUnit_iff]
    simp only [isUnit_iff_ne_zero]
  have hform (z : ZMod (p*q) × ZMod (p*q)) : F (E z) = e (z.2+c*z.1) := by
    change ((e z.2).1+(e c).1*(e z.1).1,(e z.2).2+(e c).2*(e z.1).2) = e (z.2+c*z.1)
    rw [map_add,map_mul]
    rfl
  have hproj : Set.InjOn (fun z : ZMod (p*q) × ZMod (p*q) => z.2+c*z.1) S ↔ Set.InjOn F (S.image E) := by
    constructor
    · intro hinj u hu v hv he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
      apply congrArg E
      apply hinj hx hy
      apply e.injective
      rw [←hform x,←hform y]
      exact he
    · intro hinj x hx y hy he
      apply E.injective
      apply hinj (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy)
      change x.2+c*x.1 = y.2+c*y.1 at he
      rw [hform,hform,he]
  unfold good_slopes_point_directions
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hu,hi⟩
    exact ⟨(hunit.mp hu).1,(hunit.mp hu).2,hproj.mp hi⟩
  · rintro ⟨hu,hv,hi⟩
    exact ⟨hunit.mpr ⟨hu,hv⟩,hproj.mpr hi⟩
