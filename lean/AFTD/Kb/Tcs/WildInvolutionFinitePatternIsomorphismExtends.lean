import AFTD.Prelude
import AFTD.Kb.Tcs.WildInvolutionClosedPartialIsomorphismExtends

/-!
# wild_involution_finite_pattern_isomorphism_extends

Topic: graphs   Node: 2c3aeb139628

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

Two injectively embedded copies of the same closed finite involution pattern are aligned by a global matching isomorphism, when each ambient involution has one fixed point.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem wild_involution_finite_pattern_isomorphism_extends
    {V J : Type*} [Fintype V] [Fintype J] [DecidableEq V]
    (f g : Equiv.Perm V) (hf : Function.Involutive f) (hg : Function.Involutive g)
    (a b : V) (hfa : ∀ x, f x = x ↔ x = a) (hgb : ∀ x, g x = x ↔ x = b)
    (π : Equiv.Perm J) (v w : J → V)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (hfv : ∀ j, f (v j) = v (π j)) (hgw : ∀ j, g (w j) = w (π j)) :
    ∃ e : Equiv.Perm V, (∀ x, e (f x) = g (e x)) ∧ (∀ j, e (v j) = w j) := by
  classical
  let S : Finset V := univ.image v
  let T : Finset V := univ.image w
  have hvS : ∀ j, v j ∈ S := fun j => mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have hwT : ∀ j, w j ∈ T := fun j => mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have hS : ∀ x, f x ∈ S ↔ x ∈ S := by
    intro x
    constructor
    · rintro hx
      obtain ⟨j,_,hj⟩ := mem_image.mp hx
      have heq : x = v (π j) := by rw [← hfv, hj, hf]
      rw [heq]; exact hvS _
    · intro hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hx
      rw [hfv]; exact hvS _
  have hT : ∀ x, g x ∈ T ↔ x ∈ T := by
    intro x
    constructor
    · intro hx
      obtain ⟨j,_,hj⟩ := mem_image.mp hx
      have heq : x = w (π j) := by rw [← hgw, hj, hg]
      rw [heq]; exact hwT _
    · intro hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hx
      rw [hgw]; exact hwT _
  let ev : J ≃ {x // x ∈ S} := Equiv.ofBijective (fun j => ⟨v j,hvS j⟩) (by
    constructor
    · intro i j h; exact hv (congrArg Subtype.val h)
    · intro x
      obtain ⟨j,_,hj⟩ := mem_image.mp x.property
      exact ⟨j,Subtype.ext hj⟩)
  let ew : J ≃ {x // x ∈ T} := Equiv.ofBijective (fun j => ⟨w j,hwT j⟩) (by
    constructor
    · intro i j h; exact hw (congrArg Subtype.val h)
    · intro x
      obtain ⟨j,_,hj⟩ := mem_image.mp x.property
      exact ⟨j,Subtype.ext hj⟩)
  let eS : {x // x ∈ S} ≃ {x // x ∈ T} := ev.symm.trans ew
  have hev : ∀ j, eS (ev j) = ew j := by intro j; simp [eS]
  have heS : ∀ x : {x // x ∈ S},
      (eS ⟨f x.val,(hS x.val).mpr x.property⟩).val = g (eS x).val := by
    intro x
    obtain ⟨j,rfl⟩ := ev.surjective x
    have hval : (ev j).val = v j := rfl
    have heq : (⟨f (ev j).val,(hS (ev j).val).mpr (ev j).property⟩ : {x // x ∈ S}) =
        ev (π j) := Subtype.ext (hfv j)
    rw [heq,hev,hev]
    exact (hgw j).symm
  have hmem : a ∈ S ↔ b ∈ T := by
    constructor
    · intro ha
      obtain ⟨j,_,hj⟩ := mem_image.mp ha
      have hp : π j = j := hv (by rw [← hfv,hj,(hfa a).mpr rfl])
      have hjb : w j = b := (hgb _).mp (by rw [hgw,hp])
      exact mem_image.mpr ⟨j,mem_univ _,hjb⟩
    · intro hb
      obtain ⟨j,_,hj⟩ := mem_image.mp hb
      have hp : π j = j := hw (by rw [← hgw,hj,(hgb b).mpr rfl])
      have hja : v j = a := (hfa _).mp (by rw [hfv,hp])
      exact mem_image.mpr ⟨j,mem_univ _,hja⟩
  obtain ⟨e,he,hext⟩ := wild_involution_closed_partial_isomorphism_extends
    f g hf hg a b hfa hgb S T hS hT hmem eS heS
  refine ⟨e,he,?_⟩
  intro j
  have hh := hext (ev j)
  rw [hev] at hh
  exact hh
