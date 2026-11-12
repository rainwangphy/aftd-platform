import AFTD.Prelude

/-!
# op_193_nine_cycle_stable_triples_anchored_five_coloring

Topic: graphs   Node: 5995e022de75

Provenance: helper lemma. Finite obstruction to extending the nonanchored-class argument in arXiv:2610.17884 Section 3.

The stable triples of the nine-cycle have a proper five-coloring in which every color class has an anchor intersecting each triple of the class in at least two vertices.
-/

open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def in777_fivecolorproof_anchors : Fin 5 → Finset (Fin 9) :=
  ![{0,4,6}, {1,4,8}, {1,6,8}, {2,5,7}, {3,5,7}]

private def in777_fivecolorproof_stable (S : Finset (Fin 9)) : Prop :=
  ∀ i : Fin 9, i ∈ S → i+1 ∉ S

private lemma in777_fivecolorproof_anchors_good :
    ∀ j, (in777_fivecolorproof_anchors j).card=3 ∧ in777_fivecolorproof_stable (in777_fivecolorproof_anchors j) := by
  unfold in777_fivecolorproof_stable
  decide

private lemma in777_fivecolorproof_anchored_cover :
    ∀ S : Finset (Fin 9), S.card=3 → in777_fivecolorproof_stable S →
      ∃ j : Fin 5, 2 ≤ (S ∩ in777_fivecolorproof_anchors j).card := by
  unfold in777_fivecolorproof_stable
  decide


private def in777_fivecolorproof_color (S : Finset (Fin 9)) : Fin 5 :=
  if S = in777_fivecolorproof_anchors 0 then 0 else
  if S = in777_fivecolorproof_anchors 1 then 1 else
  if S = in777_fivecolorproof_anchors 2 then 2 else
  if S = in777_fivecolorproof_anchors 3 then 3 else
  if S = in777_fivecolorproof_anchors 4 then 4 else
  if 2 ≤ (S ∩ in777_fivecolorproof_anchors 0).card then 0 else
  if 2 ≤ (S ∩ in777_fivecolorproof_anchors 1).card then 1 else
  if 2 ≤ (S ∩ in777_fivecolorproof_anchors 2).card then 2 else
  if 2 ≤ (S ∩ in777_fivecolorproof_anchors 3).card then 3 else 4

private lemma in777_fivecolorproof_anchor_color : ∀ j, in777_fivecolorproof_color (in777_fivecolorproof_anchors j)=j := by
  decide

private lemma in777_fivecolorproof_color_overlap :
    ∀ S : Finset (Fin 9), S.card=3 → in777_fivecolorproof_stable S →
      2 ≤ (S ∩ in777_fivecolorproof_anchors (in777_fivecolorproof_color S)).card := by
  unfold in777_fivecolorproof_stable
  decide

private lemma in777_fivecolorproof_anchored_five_coloring :
    ∃ (c : Finset (Fin 9) → Fin 5) (A : Fin 5 → Finset (Fin 9)),
      (∀ j, (A j).card=3 ∧ (∀ i : Fin 9, i∈A j → i+1∉A j) ∧ c (A j)=j) ∧
      (∀ S : Finset (Fin 9), S.card=3 → (∀ i : Fin 9, i∈S → i+1∉S) →
        2 ≤ (S ∩ A (c S)).card) ∧
      ∀ S T : Finset (Fin 9), S.card=3 → T.card=3 →
        (∀ i : Fin 9, i∈S → i+1∉S) → (∀ i : Fin 9, i∈T → i+1∉T) →
        Disjoint S T → c S ≠ c T := by
  refine ⟨in777_fivecolorproof_color,in777_fivecolorproof_anchors,?_,?_,?_⟩
  · intro j
    exact ⟨(in777_fivecolorproof_anchors_good j).1,(in777_fivecolorproof_anchors_good j).2,in777_fivecolorproof_anchor_color j⟩
  · exact in777_fivecolorproof_color_overlap
  · intro S T hS hT hs ht hdis heq
    have h1 := in777_fivecolorproof_color_overlap S hS hs
    have h2 := in777_fivecolorproof_color_overlap T hT ht
    rw [← heq] at h2
    let A := in777_fivecolorproof_anchors (in777_fivecolorproof_color S)
    have hsub : (S ∩ A) ∪ (T ∩ A) ⊆ A := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.mem_inter.mp h).2
      · exact (Finset.mem_inter.mp h).2
    have hd : Disjoint (S ∩ A) (T ∩ A) :=
      (Finset.disjoint_left.mpr fun x hx hy =>
        (Finset.disjoint_left.mp hdis) (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1)
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd] at hh
    have ha := (in777_fivecolorproof_anchors_good (in777_fivecolorproof_color S)).1
    dsimp [A] at hh
    omega

theorem op_193_nine_cycle_stable_triples_anchored_five_coloring :
    ∃ (c : Finset (Fin 9) → Fin 5) (A : Fin 5 → Finset (Fin 9)),
      (∀ j, (A j).card=3 ∧ (∀ i : Fin 9, i∈A j → i+1∉A j) ∧ c (A j)=j) ∧
      (∀ S : Finset (Fin 9), S.card=3 → (∀ i : Fin 9, i∈S → i+1∉S) →
        2 ≤ (S ∩ A (c S)).card) ∧
      ∀ S T : Finset (Fin 9), S.card=3 → T.card=3 →
        (∀ i : Fin 9, i∈S → i+1∉S) → (∀ i : Fin 9, i∈T → i+1∉T) →
        Disjoint S T → c S ≠ c T := by
  exact in777_fivecolorproof_anchored_five_coloring
