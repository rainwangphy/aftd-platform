import AFTD.Prelude
import AFTD.Kb.Tcs.WildInvolutionClosedPartialIsomorphismExtends

/-!
# wild_involution_partial_pattern_isomorphism_extends

Topic: graphs   Node: fe00d3492001

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

An isomorphism of arbitrary injective finite patterns, preserving every partner equality including fixed points, extends to an isomorphism of ambient involutions each having a unique fixed point.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem wild_involution_partial_pattern_isomorphism_extends
    {V J : Type*} [Fintype V] [Fintype J] [DecidableEq V]
    (f g : Equiv.Perm V) (hf : Function.Involutive f) (hg : Function.Involutive g)
    (a b : V) (hfa : ∀ x, f x = x ↔ x = a) (hgb : ∀ x, g x = x ↔ x = b)
    (v w : J → V) (hv : Function.Injective v) (hw : Function.Injective w)
    (hpattern : ∀ j k, f (v j) = v k ↔ g (w j) = w k) :
    ∃ e : Equiv.Perm V, (∀ x, e (f x) = g (e x)) ∧ (∀ j, e (v j) = w j) := by
  classical
  let uv : J × Bool → V := fun z => if z.2 then f (v z.1) else v z.1
  let uw : J × Bool → V := fun z => if z.2 then g (w z.1) else w z.1
  let flip : J × Bool → J × Bool := fun z => (z.1,!z.2)
  have hvflip : ∀ z, uv (flip z) = f (uv z) := by
    rintro ⟨j,c⟩; cases c
    · rfl
    · exact (hf (v j)).symm
  have hwflip : ∀ z, uw (flip z) = g (uw z) := by
    rintro ⟨j,c⟩; cases c
    · rfl
    · exact (hg (w j)).symm
  have hkernel : ∀ z z', uv z = uv z' ↔ uw z = uw z' := by
    rintro ⟨j,c⟩ ⟨k,d⟩
    cases c <;> cases d
    · simp only [uv,uw,Bool.false_eq_true,if_false]
      exact hv.eq_iff.trans hw.eq_iff.symm
    · simpa only [uv,uw,Bool.false_eq_true,if_false,if_true,eq_comm] using hpattern k j
    · simpa only [uv,uw,Bool.false_eq_true,if_false,if_true] using hpattern j k
    · simp only [uv,uw,if_true,f.injective.eq_iff,g.injective.eq_iff]
      exact hv.eq_iff.trans hw.eq_iff.symm
  let S : Finset V := univ.image uv
  let T : Finset V := univ.image uw
  have hvS : ∀ z, uv z ∈ S := fun z => mem_image.mpr ⟨z,mem_univ _,rfl⟩
  have hwT : ∀ z, uw z ∈ T := fun z => mem_image.mpr ⟨z,mem_univ _,rfl⟩
  have hS : ∀ x, f x ∈ S ↔ x ∈ S := by
    intro x
    constructor
    · intro hx
      obtain ⟨z,_,hz⟩ := mem_image.mp hx
      have hh : uv (flip z) = x := by rw [hvflip,hz,hf]
      exact mem_image.mpr ⟨flip z,mem_univ _,hh⟩
    · intro hx
      obtain ⟨z,_,rfl⟩ := mem_image.mp hx
      rw [← hvflip]; exact hvS _
  have hT : ∀ x, g x ∈ T ↔ x ∈ T := by
    intro x
    constructor
    · intro hx
      obtain ⟨z,_,hz⟩ := mem_image.mp hx
      have hh : uw (flip z) = x := by rw [hwflip,hz,hg]
      exact mem_image.mpr ⟨flip z,mem_univ _,hh⟩
    · intro hx
      obtain ⟨z,_,rfl⟩ := mem_image.mp hx
      rw [← hwflip]; exact hwT _
  let sv : J × Bool → {x // x ∈ S} := fun z => ⟨uv z,hvS z⟩
  let tw : J × Bool → {x // x ∈ T} := fun z => ⟨uw z,hwT z⟩
  have hsv : Function.Surjective sv := by
    intro x; obtain ⟨z,_,hz⟩ := mem_image.mp x.property
    exact ⟨z,Subtype.ext hz⟩
  have htw : Function.Surjective tw := by
    intro x; obtain ⟨z,_,hz⟩ := mem_image.mp x.property
    exact ⟨z,Subtype.ext hz⟩
  have hker : ∀ z z', sv z = sv z' ↔ tw z = tw z' := by
    intro z z'
    simpa only [Subtype.ext_iff] using hkernel z z'
  let pick : {x // x ∈ S} → J × Bool := fun x => Classical.choose (hsv x)
  have hpick : ∀ x, sv (pick x) = x := fun x => Classical.choose_spec (hsv x)
  let eS : {x // x ∈ S} ≃ {x // x ∈ T} := Equiv.ofBijective (fun x => tw (pick x)) (by
    constructor
    · intro x y h
      have hh := (hker (pick x) (pick y)).mpr h
      simpa only [hpick] using hh
    · intro y
      obtain ⟨z,rfl⟩ := htw y
      exact ⟨sv z,(hker _ _).mp (hpick (sv z))⟩)
  have heval : ∀ z, eS (sv z) = tw z := fun z => (hker _ _).mp (hpick (sv z))
  have heS : ∀ x : {x // x ∈ S},
      (eS ⟨f x.val,(hS x.val).mpr x.property⟩).val = g (eS x).val := by
    intro x
    obtain ⟨z,rfl⟩ := hsv x
    have hh : (⟨f (sv z).val,(hS (sv z).val).mpr (sv z).property⟩ : {x // x ∈ S}) =
        sv (flip z) := Subtype.ext (hvflip z).symm
    rw [hh,heval,heval]
    exact hwflip z
  have hmem : a ∈ S ↔ b ∈ T := by
    constructor
    · intro ha
      let x : {x // x ∈ S} := ⟨a,ha⟩
      have heq : (⟨f x.val,(hS x.val).mpr x.property⟩ : {x // x ∈ S}) = x :=
        Subtype.ext ((hfa a).mpr rfl)
      have hh := heS x
      rw [heq] at hh
      have hb : (eS x).val = b := (hgb _).mp hh.symm
      exact hb ▸ (eS x).property
    · intro hb
      obtain ⟨x,hx⟩ := eS.surjective ⟨b,hb⟩
      have hh := heS x
      have hxval : (eS x).val = b := congrArg Subtype.val hx
      rw [hxval,(hgb b).mpr rfl] at hh
      have hfix : f x.val = x.val := by
        have hsub : (⟨f x.val,(hS x.val).mpr x.property⟩ : {x // x ∈ S}) = x := by
          apply eS.injective
          apply Subtype.ext
          exact hh.trans hxval.symm
        exact congrArg Subtype.val hsub
      have ha : x.val = a := (hfa _).mp hfix
      exact ha ▸ x.property
  obtain ⟨e,he,hext⟩ := wild_involution_closed_partial_isomorphism_extends
    f g hf hg a b hfa hgb S T hS hT hmem eS heS
  refine ⟨e,he,?_⟩
  intro j
  have hh := hext (sv (j,false))
  rw [heval] at hh
  exact hh
