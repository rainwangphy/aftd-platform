import AFTD.Prelude

/-!
# finite_maximum_packing_conflicts_satisfy_hall

Topic: graphs   Node: 5ee724b5a01c

Provenance: helper lemma. Elementary packing exchange and matching condition; related to the packing definitions in arXiv:2610.15539, Section 1.

Given a maximum packing P and any packing W of a finite set family, every subpacking X of W meets at least |X| members of P. Thus the bipartite intersection graph from W to P satisfies the matching condition.
-/

theorem finite_maximum_packing_conflicts_satisfy_hall
    {α : Type*} [DecidableEq α] (F P W : Finset (Finset α))
    (hnonempty : ∀ t ∈ F, t.Nonempty)
    (hPF : P ⊆ F) (hWF : W ⊆ F)
    (hPdis : (P : Set (Finset α)).Pairwise Disjoint)
    (hWdis : (W : Set (Finset α)).Pairwise Disjoint)
    (hmax : ∀ Q : Finset (Finset α), Q ⊆ F →
      (Q : Set (Finset α)).Pairwise Disjoint → Q.card ≤ P.card) :
    ∀ X : Finset (Finset α), X ⊆ W →
      X.card ≤ (P.filter fun s => ¬ Disjoint s (X.biUnion id)).card := by
  open Finset in
  intro X hXW
  let p := fun s : Finset α => Disjoint s (X.biUnion id)
  let P0 := P.filter p
  let N := P.filter (fun s => ¬ p s)
  have hP0F : P0 ⊆ F := (filter_subset p P).trans hPF
  have hXF : X ⊆ F := hXW.trans hWF
  have hQF : P0 ∪ X ⊆ F := union_subset hP0F hXF
  have hdisj : Disjoint P0 X := by
    rw [disjoint_left]
    intro t htP0 htX
    have h1 : Disjoint t (X.biUnion id) := (mem_filter.mp htP0).2
    have h2 : t ⊆ X.biUnion id := subset_biUnion_of_mem id htX
    have h3 : Disjoint t t := Disjoint.mono_right h2 h1
    have h4 : t = ∅ := disjoint_self.mp h3
    have h5 : t ∈ F := hXF htX
    have h6 : t.Nonempty := hnonempty t h5
    exact h6.ne_empty h4
  have hcross : ∀ a ∈ P0, ∀ b ∈ X, Disjoint a b := by
    intro a ha b hb
    have ha' : Disjoint a (X.biUnion id) := (mem_filter.mp ha).2
    exact Disjoint.mono_right (subset_biUnion_of_mem id hb) ha'
  have hP0_pair : (P0 : Set (Finset α)).Pairwise Disjoint :=
    Set.Pairwise.mono (coe_subset.mpr (filter_subset p P)) hPdis
  have hX_pair : (X : Set (Finset α)).Pairwise Disjoint :=
    Set.Pairwise.mono (coe_subset.mpr hXW) hWdis
  have hQ_pair : ((P0 ∪ X : Finset (Finset α)) : Set (Finset α)).Pairwise Disjoint := by
    intro a ha b hb hab
    rw [mem_coe, mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hP0_pair ha hb hab
    · exact hcross a ha b hb
    · exact (hcross b hb a ha).symm
    · exact hX_pair ha hb hab
  have hQ_card : (P0 ∪ X).card = P0.card + X.card := card_union_of_disjoint hdisj
  have hle : (P0 ∪ X).card ≤ P.card := hmax (P0 ∪ X) hQF hQ_pair
  have hP_split : P0.card + N.card = P.card := by
    have := @card_filter_add_card_filter_not (Finset α) P p _ _
    exact this
  rw [hQ_card] at hle
  rw [← hP_split] at hle
  exact Nat.le_of_add_le_add_left hle
