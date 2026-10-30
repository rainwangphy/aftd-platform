import AFTD.Prelude
import AFTD.Kb.Tcs.WildInvolutionsConjugateOfFixedCount

/-!
# wild_involutions_equiv_of_card_and_fixed_count

Topic: graphs   Node: f2a3c5ee7d62

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

Cross-type version of finite involution conjugacy: equal finite cardinalities and equal fixed-point counts give an intertwining equivalence.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem wild_involutions_equiv_of_card_and_fixed_count
    {V W : Type*} [Fintype V] [Fintype W]
    (f : Equiv.Perm V) (g : Equiv.Perm W)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hcard : Fintype.card V = Fintype.card W)
    (hfix : (univ.filter fun x => f x = x).card =
      (univ.filter fun y => g y = y).card) :
    ∃ e : V ≃ W, ∀ x, e (f x) = g (e x) := by
  classical
  let e₀ : V ≃ W := Fintype.equivOfCardEq hcard
  let g' : Equiv.Perm V := (e₀.trans g).trans e₀.symm
  have hg' : Function.Involutive g' := by
    intro x
    simp only [g',Equiv.trans_apply,Equiv.apply_symm_apply]
    rw [hg,Equiv.symm_apply_apply]
  have hgc : (univ.filter fun x => g' x = x).card =
      (univ.filter fun y => g y = y).card := by
    apply card_bij (fun x _ => e₀ x)
    · intro x hx
      simp only [mem_filter,mem_univ,true_and] at hx ⊢
      have hh := congrArg e₀ hx
      simpa [g'] using hh
    · intro x _ y _ h
      exact e₀.injective h
    · intro y hy
      refine ⟨e₀.symm y,?_,e₀.apply_symm_apply y⟩
      simp only [mem_filter,mem_univ,true_and] at hy ⊢
      simp [g',hy]
  obtain ⟨c,hc⟩ := wild_involutions_conjugate_of_fixed_count f g' hf hg'
    (hfix.trans hgc.symm)
  refine ⟨c.trans e₀,?_⟩
  intro x
  have hh := congrArg e₀ (hc x)
  simpa [g'] using hh
