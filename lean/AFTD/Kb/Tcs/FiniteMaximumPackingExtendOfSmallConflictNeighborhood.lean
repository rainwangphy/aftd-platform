import AFTD.Prelude

/-!
# finite_maximum_packing_extend_of_small_conflict_neighborhood

Topic: graphs   Node: 62088d5d9e84

Provenance: helper lemma. Elementary packing exchange in the triangle packing-cover campaign, related to arXiv:2610.15539, Section 1.

A packing W in a finite set family extends to a maximum packing if it intersects no more members of a fixed maximum packing P than W has members.
-/

theorem finite_maximum_packing_extend_of_small_conflict_neighborhood
    {α : Type*} [DecidableEq α] (F P W : Finset (Finset α))
    (hnonempty : ∀ t ∈ F, t.Nonempty)
    (hPF : P ⊆ F) (hWF : W ⊆ F)
    (hPdis : (P : Set (Finset α)).Pairwise Disjoint)
    (hWdis : (W : Set (Finset α)).Pairwise Disjoint)
    (hmax : ∀ Q : Finset (Finset α), Q ⊆ F →
      (Q : Set (Finset α)).Pairwise Disjoint → Q.card ≤ P.card)
    (hconf : (P.filter fun s => ¬ Disjoint s (W.biUnion id)).card ≤ W.card) :
    ∃ Q : Finset (Finset α), Q ⊆ F ∧
      (Q : Set (Finset α)).Pairwise Disjoint ∧ Q.card = P.card ∧ W ⊆ Q := by
  open Finset in
  set N := P.filter fun s => ¬ Disjoint s (W.biUnion id)
  set Q := (P \ N) ∪ W
  have hQF : Q ⊆ F := Finset.union_subset (Finset.sdiff_subset.trans hPF) hWF
  have hQdis : (Q : Set (Finset α)).Pairwise Disjoint := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    change a ∈ (P \ N) ∪ W at ha
    change b ∈ (P \ N) ∪ W at hb
    rw [Finset.mem_union] at ha hb
    rcases ha with ha | haW
    · rw [Finset.mem_sdiff, Finset.mem_filter, not_and, not_not] at ha
      rcases hb with hb | hbW
      · rw [Finset.mem_sdiff] at hb
        exact hPdis ha.1 hb.1 hab
      · have hd := ha.2 ha.1
        rw [Finset.disjoint_biUnion_right] at hd
        exact hd b hbW
    · rcases hb with hb | hbW
      · rw [Finset.mem_sdiff, Finset.mem_filter, not_and, not_not] at hb
        have hd := hb.2 hb.1
        rw [Finset.disjoint_biUnion_right] at hd
        exact (hd a haW).symm
      · exact hWdis haW hbW hab
  have hdisj : Disjoint (P \ N) W := by
    rw [Finset.disjoint_left]
    intro x hx hxW
    rw [Finset.mem_sdiff, Finset.mem_filter, not_and, not_not] at hx
    have hd := hx.2 hx.1
    rw [Finset.disjoint_biUnion_right] at hd
    have hxx : Disjoint x x := hd x hxW
    have he : x = ∅ := disjoint_self.mp hxx
    have hne : x.Nonempty := hnonempty x (hWF hxW)
    exact hne.ne_empty he
  have hQcard : Q.card = P.card := by
    have h1 : Q.card ≤ P.card := hmax Q hQF hQdis
    have h2 : Q.card = (P \ N).card + W.card := Finset.card_union_of_disjoint hdisj
    have h3 : (P \ N).card = P.card - N.card := Finset.card_sdiff_of_subset (Finset.filter_subset _ P)
    have h4 : N.card ≤ P.card := Finset.card_le_card (Finset.filter_subset _ P)
    have h5 : P.card ≤ Q.card := by
      rw [h2, h3]
      omega
    exact le_antisymm h1 h5
  exact ⟨Q, hQF, hQdis, hQcard, Finset.subset_union_right⟩
