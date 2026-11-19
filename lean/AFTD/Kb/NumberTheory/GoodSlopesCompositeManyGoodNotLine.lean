import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections

/-!
# good_slopes_composite_many_good_not_line

Topic: elementary_number_theory   Node: 6c24253e7d80

Provenance: helper lemma. Computed obstruction to extending the prime-field direction classification in OP-1027; experiment 32044.

There is a set of 33 points over the residues modulo 33 with more than ten good unit directions, although it is neither vertical nor contained in any affine line y+ax=t.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
private def in962_f33 (x : ZMod 33) : ZMod 33 := if x.val % 3 = 0 then 2*x else 12*x
private def in962_G33 : Finset (ZMod 33) := {1,2,4,5,7,8,13,14,16,17,19}
private theorem in962_G33_card : in962_G33.card = 11 := by decide
private theorem in962_f33_0 : in962_f33 0 = 0 := by decide
private theorem in962_f33_1 : in962_f33 1 = 12 := by decide
private theorem in962_f33_3 : in962_f33 3 = 6 := by decide
private theorem in962_G33_good : ∀ a : ZMod 33, a ∈ in962_G33 →
    (∃ b : ZMod 33, a*b=1) ∧ Function.Injective (fun x : ZMod 33 => in962_f33 x + a*x) := by
  decide

theorem good_slopes_composite_many_good_not_line :
    ∃ S : Finset (ZMod 33 × ZMod 33), S.card = 33 ∧
      10 < (good_slopes_point_directions 33 S).card ∧
      ¬ ((∃ x : ZMod 33, ∀ p ∈ S, p.1=x) ∨
        (∃ a t : ZMod 33, ∀ p ∈ S, p.2+a*p.1=t)) := by
  classical
  let F (x : ZMod 33) : ZMod 33 × ZMod 33 := (x,in962_f33 x)
  let S := Finset.univ.image F
  have hF : Function.Injective F := by
    intro x y h
    exact congrArg Prod.fst h
  have hcard : S.card = 33 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hF,Finset.card_univ,ZMod.card]
  have hG : in962_G33 ⊆ good_slopes_point_directions 33 S := by
    intro a ha
    have hc := in962_G33_good a ha
    unfold good_slopes_point_directions
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨isUnit_iff_exists_inv.mpr hc.1, ?_⟩
    intro p hp q hq he
    obtain ⟨x,hx0,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy0,rfl⟩ := Finset.mem_image.mp hq
    apply congrArg F
    apply hc.2
    exact he
  have hcount : 10 < (good_slopes_point_directions 33 S).card := by
    have h := Finset.card_le_card hG
    rw [in962_G33_card] at h
    omega
  have h0 : ((0 : ZMod 33),0) ∈ S := by
    apply Finset.mem_image.mpr
    refine ⟨0,Finset.mem_univ _, ?_⟩
    simp [F,in962_f33_0]
  have h1 : ((1 : ZMod 33),12) ∈ S := by
    apply Finset.mem_image.mpr
    refine ⟨1,Finset.mem_univ _, ?_⟩
    simp [F,in962_f33_1]
  have h3 : ((3 : ZMod 33),6) ∈ S := by
    apply Finset.mem_image.mpr
    refine ⟨3,Finset.mem_univ _, ?_⟩
    simp [F,in962_f33_3]
  refine ⟨S,hcard,hcount, ?_⟩
  rintro (⟨x,hx⟩ | ⟨a,t,ht⟩)
  · have h01 : (0 : ZMod 33) = 1 := (hx _ h0).trans (hx _ h1).symm
    exact (by decide : (0 : ZMod 33) ≠ 1) h01
  · have q0 := ht _ h0
    have q1 := ht _ h1
    have q3 := ht _ h3
    have h33 : (33 : ZMod 33) = 0 := ZMod.natCast_self 33
    have hh : (3 : ZMod 33) = 0 := by linear_combination q3-3*q1+2*q0+h33
    exact (by decide : (3 : ZMod 33) ≠ 0) hh
