import AFTD.Prelude

/-!
# op874_four_two_incidence_cover

Topic: graphs   Node: 7f524c14cde5

Provenance: helper lemma. OP-874: required same-bit factor edges and matching-owned ports via the finite matching criterion

In a finite incidence system with four edges at every left vertex and two vertices at every edge, any edge subset of left degree at most two can be covered while choosing a different incident edge for every left vertex.
-/

open Finset

theorem op874_four_two_incidence_cover {L E : Type*} [Fintype L] [Fintype E] [DecidableEq L] [DecidableEq E] (inc : L → E → Prop) [DecidableRel inc] (S : Finset E) (hleft : ∀ l, (Finset.univ.filter (fun e => inc l e)).card = 4) (hright : ∀ e, (Finset.univ.filter (fun l => inc l e)).card = 2) (hS : ∀ l, (S.filter (fun e => inc l e)).card ≤ 2) : ∃ f : L → E, Function.Injective f ∧ (∀ l, inc l (f l)) ∧ ∀ e ∈ S, ∃ l, f l = e := by
  classical
  have heq : Fintype.card E = 2 * Fintype.card L := by
    have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := (Finset.univ : Finset L)) (t := (Finset.univ : Finset E)) inc
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, hleft, hright,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at hh
    omega
  let N : Finset L → Finset E := fun A => Finset.univ.filter (fun e => ∃ l ∈ A, inc l e)
  have hN (A : Finset L) : 4 * A.card ≤ 2 * (N A).card := by
    have h := Finset.card_nsmul_le_card_nsmul (R := ℕ) (m := 4) (n := 2) (s := A) (t := N A) inc
      (by
        intro l hl
        have he : (N A).filter (fun e => inc l e) = Finset.univ.filter (fun e => inc l e) := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, N]
          constructor
          · exact fun h => h.2
          · intro he; exact ⟨⟨l, hl, he⟩, he⟩
        simpa [Finset.bipartiteAbove, he, hleft l])
      (by
        intro e he
        have hh : (A.filter (fun l => inc l e)).card ≤ (Finset.univ.filter (fun l => inc l e)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
        simpa [Finset.bipartiteBelow, hright e] using hh)
    simpa only [nsmul_eq_mul, Nat.mul_comm, Nat.cast_id] using h
  have hbad (A : Finset L) : (S \ N A).card ≤ (Finset.univ \ A).card := by
    have h := Finset.card_nsmul_le_card_nsmul (R := ℕ) (m := 2) (n := 2)
      (s := S \ N A) (t := Finset.univ \ A) (fun e l => inc l e)
      (by
        intro e he
        have heN : e ∉ N A := (Finset.mem_sdiff.mp he).2
        have heq' : (Finset.univ \ A).filter (fun l => inc l e) = Finset.univ.filter (fun l => inc l e) := by
          ext l; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro hil
            have hn : l ∉ A := by
              intro hl
              apply heN
              simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨l, hl, hil⟩
            exact ⟨hn, hil⟩
        simpa [Finset.bipartiteAbove, heq', hright e])
      (by
        intro l hl
        have hh : ((S \ N A).filter (fun e => inc l e)).card ≤ (S.filter (fun e => inc l e)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset))
        exact (by simpa [Finset.bipartiteBelow] using hh.trans (hS l)))
    simp only [nsmul_eq_mul, Nat.cast_id] at h
    omega
  let choices : L ⊕ L → Finset E := fun x =>
    match x with
    | .inl l => Finset.univ.filter (fun e => inc l e)
    | .inr _ => Finset.univ \ S
  have hcriterion : ∀ T : Finset (L ⊕ L), T.card ≤ (T.biUnion choices).card := by
    intro T
    let A := T.toLeft
    let B := T.toRight
    have hAB : A.card + B.card = T.card := Finset.card_toLeft_add_card_toRight
    have hB : B.card ≤ Fintype.card L := by simpa using Finset.card_le_univ B
    have hA : A.card ≤ Fintype.card L := by simpa using Finset.card_le_univ A
    have hAc : (Finset.univ \ A).card + A.card = Fintype.card L := by
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    have hNsub : N A ⊆ T.biUnion choices := by
      intro e he
      obtain ⟨_, l, hl, hle⟩ := Finset.mem_filter.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨Sum.inl l, ?_, ?_⟩
      · exact Finset.mem_toLeft.mp hl
      · simp [choices, hle]
    by_cases hB0 : B.Nonempty
    · obtain ⟨l, hl⟩ := hB0
      have hcomp : (Finset.univ \ (S \ N A)) ⊆ T.biUnion choices := by
        intro e he
        have he' : e ∉ S ∨ e ∈ N A := by
          by_cases hs : e ∈ S
          · right
            by_contra hn
            exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mpr ⟨hs, hn⟩)
          · exact Or.inl hs
        rcases he' with hnot | hN'
        · apply Finset.mem_biUnion.mpr
          refine ⟨Sum.inr l, Finset.mem_toRight.mp hl, ?_⟩
          simp [choices, hnot]
        · exact hNsub hN'
      have hcb := Finset.card_le_card hcomp
      have hbad' := hbad A
      have hbadsub : S \ N A ⊆ (Finset.univ : Finset E) := Finset.subset_univ _
      have hcard : (Finset.univ \ (S \ N A)).card + (S \ N A).card = Fintype.card E := by
        simpa using Finset.card_sdiff_add_card_eq_card hbadsub
      omega
    · have hBz : B.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hB0)
      have hn := hN A
      have hh := Finset.card_le_card hNsub
      omega
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp hcriterion
  have hc : Fintype.card (L ⊕ L) = Fintype.card E := by simp [Fintype.card_sum, heq, two_mul]
  have hsurj := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hc⟩ |>.2
  refine ⟨fun l => f (Sum.inl l), ?_, ?_, ?_⟩
  · intro a b hab
    exact Sum.inl.inj (hfinj hab)
  · intro l
    simpa [choices] using hfmem (Sum.inl l)
  · intro e he
    obtain ⟨x, hx⟩ := hsurj e
    cases x with
    | inl l => exact ⟨l, hx⟩
    | inr l =>
      have hm := hfmem (Sum.inr l)
      simp only [choices, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm
      exact False.elim (hm (hx ▸ he))
