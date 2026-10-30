import AFTD.Prelude
import AFTD.Kb.Tcs.WildInvolutionsEquivOfCardAndFixedCount

/-!
# wild_involution_closed_partial_isomorphism_extends

Topic: graphs   Node: eeecb4c2b0fa

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

A matching isomorphism on closed finite subsets extends globally when both involutions have a unique fixed point and the subsets either both contain or both omit that point.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem wild_involution_closed_partial_isomorphism_extends
    {V : Type*} [Fintype V] [DecidableEq V]
    (f g : Equiv.Perm V) (hf : Function.Involutive f) (hg : Function.Involutive g)
    (a b : V) (hfa : ∀ x, f x = x ↔ x = a) (hgb : ∀ x, g x = x ↔ x = b)
    (S T : Finset V) (hS : ∀ x, f x ∈ S ↔ x ∈ S)
    (hT : ∀ x, g x ∈ T ↔ x ∈ T)
    (hmem : a ∈ S ↔ b ∈ T)
    (eS : {x // x ∈ S} ≃ {x // x ∈ T})
    (heS : ∀ x : {x // x ∈ S},
      (eS ⟨f x.val,(hS x.val).mpr x.property⟩).val = g (eS x).val) :
    ∃ e : Equiv.Perm V, (∀ x, e (f x) = g (e x)) ∧
      (∀ x : {x // x ∈ S}, e x.val = (eS x).val) := by
  classical
  let fC : Equiv.Perm {x : V // x ∉ S} :=
    f.subtypeEquiv (fun x => (not_congr (hS x)).symm)
  let gC : Equiv.Perm {x : V // x ∉ T} :=
    g.subtypeEquiv (fun x => (not_congr (hT x)).symm)
  have hfC : Function.Involutive fC := by
    intro x; apply Subtype.ext; exact hf x.val
  have hgC : Function.Involutive gC := by
    intro x; apply Subtype.ext; exact hg x.val
  have hcard : Fintype.card {x : V // x ∉ S} = Fintype.card {x : V // x ∉ T} := by
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_compl,Fintype.card_congr eS]
  have hfixedS : (univ.filter fun x : {x : V // x ∉ S} => fC x = x).card =
      (univ.filter fun x : V => x ∉ S ∧ x = a).card := by
    apply card_bij (fun x _ => x.val)
    · intro x hx
      simp only [mem_filter,mem_univ,true_and] at hx ⊢
      exact ⟨x.property,(hfa x.val).mp (congrArg Subtype.val hx)⟩
    · intro x _ y _ h; exact Subtype.ext h
    · intro x hx
      simp only [mem_filter,mem_univ,true_and] at hx
      refine ⟨⟨x,hx.1⟩,?_,rfl⟩
      simp only [mem_filter,mem_univ,true_and]
      apply Subtype.ext
      exact (hfa x).mpr hx.2
  have hfixedT : (univ.filter fun x : {x : V // x ∉ T} => gC x = x).card =
      (univ.filter fun x : V => x ∉ T ∧ x = b).card := by
    apply card_bij (fun x _ => x.val)
    · intro x hx
      simp only [mem_filter,mem_univ,true_and] at hx ⊢
      exact ⟨x.property,(hgb x.val).mp (congrArg Subtype.val hx)⟩
    · intro x _ y _ h; exact Subtype.ext h
    · intro x hx
      simp only [mem_filter,mem_univ,true_and] at hx
      refine ⟨⟨x,hx.1⟩,?_,rfl⟩
      simp only [mem_filter,mem_univ,true_and]
      apply Subtype.ext
      exact (hgb x).mpr hx.2
  have hfixed : (univ.filter fun x : {x : V // x ∉ S} => fC x = x).card =
      (univ.filter fun x : {x : V // x ∉ T} => gC x = x).card := by
    rw [hfixedS,hfixedT]
    simp only [filter_and,filter_eq',mem_univ]
    simp [inter_comm,singleton_inter,hmem]
    split <;> simp
  obtain ⟨eC,heC⟩ := wild_involutions_equiv_of_card_and_fixed_count
    fC gC hfC hgC hcard (by
      convert hfixed using 1 <;> congr 1 <;> ext x <;> simp)
  let e : Equiv.Perm V := ((Equiv.sumCompl (fun x => x ∈ S)).symm.trans
    (Equiv.sumCongr eS eC)).trans (Equiv.sumCompl (fun x => x ∈ T))
  have hleft : ∀ x (hx : x ∈ S), e x = (eS ⟨x,hx⟩).val := by
    intro x hx
    simp [e,Equiv.sumCompl_symm_apply_of_pos hx]
  have hright : ∀ x (hx : x ∉ S), e x = (eC ⟨x,hx⟩).val := by
    intro x hx
    simp [e,Equiv.sumCompl_symm_apply_of_neg hx]
  refine ⟨e,?_,fun x => hleft x.val x.property⟩
  intro x
  by_cases hx : x ∈ S
  · rw [hleft x hx,hleft (f x) ((hS x).mpr hx)]
    exact heS ⟨x,hx⟩
  · have hfx : f x ∉ S := (not_congr (hS x)).mpr hx
    rw [hright x hx,hright (f x) hfx]
    exact congrArg Subtype.val (heC ⟨x,hx⟩)
