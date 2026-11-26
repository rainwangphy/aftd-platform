import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FourTwoIncidenceCount
import AFTD.Kb.Tcs.Op874FourTwoSlotHall

/-!
# op874_four_two_incidence_two_pseudoforest_cover

Topic: graphs   Node: cac12d044d27

Provenance: helper lemma. Low-port and pseudoforest decomposition for OP-874, https://arxiv.org/abs/2610.41950.

In a finite four-by-two incidence system, if every left vertex meets at most two required edges, the edges split into two injective incident assignments, one covering every required edge and one containing none of them.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem op874_four_two_incidence_two_pseudoforest_cover
    {L E : Type*} [Fintype L] [Fintype E] [DecidableEq L] [DecidableEq E]
    (inc : L → E → Prop) [DecidableRel inc] (S : Finset E)
    (hleft : ∀ l, (Finset.univ.filter fun e => inc l e).card = 4)
    (hright : ∀ e, (Finset.univ.filter fun l => inc l e).card = 2)
    (hS : ∀ l, (S.filter fun e => inc l e).card ≤ 2) :
    ∃ f g : L → E, Function.Injective f ∧ Function.Injective g ∧
      (∀ l, inc l (f l) ∧ inc l (g l) ∧ g l ∉ S) ∧
      (∀ x y, f x ≠ g y) ∧ ∀ e ∈ S, ∃ l, f l = e := by
  classical
  let choices : E → Finset (L × Bool) := fun e =>
    univ.filter fun p => inc p.1 e ∧ (e ∈ S → p.2 = false)
  have hhall : ∀ X : Finset E, X.card ≤ (X.biUnion choices).card :=
    fun X => op874_four_two_slot_hall inc S hleft hright hS X
  obtain ⟨m, hminj, hm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp hhall
  have hcard : Fintype.card E = Fintype.card (L × Bool) := by
    have h := op874_four_two_incidence_count inc hright (univ : Finset E)
    simp only [hleft, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_prod, Fintype.card_bool] at h ⊢
    simp only [Nat.cast_id] at h
    omega
  have hmsurj : Function.Surjective m := ((Fintype.bijective_iff_injective_and_card m).2 ⟨hminj,hcard⟩).2
  let inv : L × Bool → E := fun p => Classical.choose (hmsurj p)
  have hinv : ∀ p, m (inv p) = p := fun p => Classical.choose_spec (hmsurj p)
  let f : L → E := fun l => inv (l,false)
  let g : L → E := fun l => inv (l,true)
  have hf : Function.Injective f := by
    intro x y h
    have := congrArg m h
    simp only [f, hinv, Prod.mk.injEq, and_true] at this
    exact this
  have hg : Function.Injective g := by
    intro x y h
    have := congrArg m h
    simp only [g, hinv, Prod.mk.injEq, and_true] at this
    exact this
  refine ⟨f,g,hf,hg,?_,?_,?_⟩
  · intro l
    have h0 := hm (f l)
    have h1 := hm (g l)
    simp only [choices, mem_filter, mem_univ, true_and] at h0 h1
    rw [show m (f l) = (l,false) from hinv _] at h0
    rw [show m (g l) = (l,true) from hinv _] at h1
    simp only [Prod.fst, Prod.snd, Bool.true_eq_false, imp_false] at h0 h1
    exact ⟨h0.1,h1.1,h1.2⟩
  · intro x y h
    have := congrArg m h
    simp only [f,g,hinv,Prod.mk.injEq,Bool.false_eq_true,and_false] at this
  · intro e he
    have h := hm e
    simp only [choices,mem_filter,mem_univ,true_and] at h
    have hb := h.2 he
    refine ⟨(m e).1, ?_⟩
    apply hminj
    rw [show m (f (m e).1) = ((m e).1,false) from hinv _]
    cases hme : m e with
    | mk l b => simp only [hme, Prod.fst, Prod.snd] at hb ⊢; subst b; rfl
