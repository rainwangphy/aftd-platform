import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FourTwoIncidenceCount

/-!
# op874_four_two_slot_hall

Topic: graphs   Node: 4032c2385fe9

Provenance: helper lemma. Incidence and matching reduction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

In a four-by-two incidence system with at most two required edges at each left vertex, every edge set has enough allowed first and second slots for an injective assignment.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem op874_four_two_slot_hall
    {L E : Type*} [Fintype L] [Fintype E] [DecidableEq L] [DecidableEq E]
    (inc : L → E → Prop) [DecidableRel inc] (S : Finset E)
    (hleft : ∀ l, (univ.filter fun e => inc l e).card = 4)
    (hright : ∀ e, (univ.filter fun l => inc l e).card = 2)
    (hS : ∀ l, (S.filter fun e => inc l e).card ≤ 2)
    (X : Finset E) :
    X.card ≤ (X.biUnion fun e => univ.filter fun p : L × Bool =>
      inc p.1 e ∧ (e ∈ S → p.2 = false)).card := by
  classical
  let A : Finset L := univ.filter fun l => ∃ e ∈ X, inc l e
  let B : Finset L := univ.filter fun l => ∃ e ∈ X, e ∉ S ∧ inc l e
  let d : L → ℕ := fun l => (X.filter fun e => inc l e).card
  have hBA : B ⊆ A := by
    intro l hl
    simp only [B, A, mem_filter, mem_univ, true_and] at hl ⊢
    obtain ⟨e, he, -, hi⟩ := hl
    exact ⟨e, he, hi⟩
  have hdn : ∀ l, l ∉ A → d l = 0 := by
    intro l hl
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hx := mem_filter.mp he
    apply hl
    simp only [A, mem_filter, mem_univ, true_and]
    exact ⟨e, hx.1, hx.2⟩
  have hd4 : ∀ l, d l ≤ 4 := by
    intro l
    calc
      d l ≤ (univ.filter fun e => inc l e).card := by
        apply Finset.card_le_card
        intro e he
        simp only [mem_filter, mem_univ, true_and] at he ⊢
        exact he.2
      _ = 4 := hleft l
  have hd2 : ∀ l ∈ A \ B, d l ≤ 2 := by
    intro l hl
    have hnot : l ∉ B := (mem_sdiff.mp hl).2
    calc
      d l ≤ (S.filter fun e => inc l e).card := by
        apply Finset.card_le_card
        intro e he
        simp only [d, mem_filter] at he
        simp only [mem_filter]
        refine ⟨?_, he.2⟩
        by_contra hn
        apply hnot
        simp only [B, mem_filter, mem_univ, true_and]
        exact ⟨e, he.1, hn, he.2⟩
      _ ≤ 2 := hS l
  have hsum0 : (∑ l : L, d l) = ∑ l ∈ A, d l := by
    symm
    apply Finset.sum_subset (Finset.subset_univ A)
    intro l _ hl
    exact hdn l hl
  have hsum : (∑ l : L, d l) = (∑ l ∈ A \ B, d l) + ∑ l ∈ B, d l := by
    rw [hsum0, Finset.sum_sdiff hBA]
  have hbound1 : (∑ l ∈ A \ B, d l) ≤ 2 * (A \ B).card := by
    calc
      _ ≤ ∑ _l ∈ A \ B, 2 := Finset.sum_le_sum (by intro l hl; exact hd2 l hl)
      _ = _ := by simp [mul_comm]
  have hbound2 : (∑ l ∈ B, d l) ≤ 4 * B.card := by
    calc
      _ ≤ ∑ _l ∈ B, 4 := Finset.sum_le_sum (by intro l _; exact hd4 l)
      _ = _ := by simp [mul_comm]
  have hdouble := op874_four_two_incidence_count inc hright X
  change (∑ l : L, d l) = 2 * X.card at hdouble
  have hcardAB : (A \ B).card + B.card = A.card := Finset.card_sdiff_add_card_eq_card hBA
  have hineq : X.card ≤ A.card + B.card := by omega
  let slots : Finset (L × Bool) :=
    A.image (fun l => (l,false)) ∪ B.image (fun l => (l,true))
  have hdisj : Disjoint (A.image (fun l => (l,false))) (B.image (fun l => (l,true))) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_image.mp hp with ⟨a, -, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨b, -, he⟩
    have := congrArg Prod.snd he
    cases this
  have hslots : slots.card = A.card + B.card := by
    dsimp [slots]
    rw [Finset.card_union_of_disjoint hdisj]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h),
        Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h)]
  have hsub : slots ⊆ X.biUnion (fun e => univ.filter fun p : L × Bool =>
      inc p.1 e ∧ (e ∈ S → p.2 = false)) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_image.mp hp with ⟨l, hl, rfl⟩
      simp only [A, mem_filter, mem_univ, true_and] at hl
      obtain ⟨e, he, hi⟩ := hl
      simp only [mem_biUnion, mem_filter, mem_univ, true_and]
      exact ⟨e, he, hi, by simp⟩
    · rcases Finset.mem_image.mp hp with ⟨l, hl, rfl⟩
      simp only [B, mem_filter, mem_univ, true_and] at hl
      obtain ⟨e, he, hn, hi⟩ := hl
      simp only [mem_biUnion, mem_filter, mem_univ, true_and]
      exact ⟨e, he, hi, by intro hs; exact (hn hs).elim⟩
  calc
    X.card ≤ A.card + B.card := hineq
    _ = slots.card := hslots.symm
    _ ≤ _ := Finset.card_le_card hsub
