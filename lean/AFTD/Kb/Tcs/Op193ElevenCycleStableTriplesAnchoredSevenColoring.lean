import AFTD.Prelude

/-!
# op_193_eleven_cycle_stable_triples_anchored_seven_coloring

Topic: graphs   Node: 9fe09065af7c

Provenance: helper lemma. Finite obstruction to the nonanchored-class method; experiment 23358.

The stable triples of the eleven-cycle admit a proper seven-coloring in which each color class has an anchor meeting every triple in that class in at least two vertices.
-/

open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

private def in777e_anchors : Fin 7 → Finset (Fin 11) :=
  ![{0,3,8}, {0,2,7}, {4,6,9}, {3,7,10}, {1,5,9}, {2,8,10}, {1,4,6}]

private def in777e_stable (S : Finset (Fin 11)) : Prop :=
  ∀ i : Fin 11, i ∈ S → i+1 ∉ S

lemma in777e_anchors_good :
    ∀ j, (in777e_anchors j).card=3 ∧ in777e_stable (in777e_anchors j) := by
  unfold in777e_stable
  decide

lemma in777e_anchored_cover :
    ∀ S : Finset (Fin 11), S.card=3 → in777e_stable S →
      ∃ j : Fin 7, 2 ≤ (S ∩ in777e_anchors j).card := by
  unfold in777e_stable
  decide


private def in777e_color (S : Finset (Fin 11)) : Fin 7 :=
  if S = in777e_anchors 0 then 0 else
  if S = in777e_anchors 1 then 1 else
  if S = in777e_anchors 2 then 2 else
  if S = in777e_anchors 3 then 3 else
  if S = in777e_anchors 4 then 4 else
  if S = in777e_anchors 5 then 5 else
  if S = in777e_anchors 6 then 6 else
  if 2 ≤ (S ∩ in777e_anchors 0).card then 0 else
  if 2 ≤ (S ∩ in777e_anchors 1).card then 1 else
  if 2 ≤ (S ∩ in777e_anchors 2).card then 2 else
  if 2 ≤ (S ∩ in777e_anchors 3).card then 3 else
  if 2 ≤ (S ∩ in777e_anchors 4).card then 4 else
  if 2 ≤ (S ∩ in777e_anchors 5).card then 5 else
  6

private lemma in777e_anchor_color : ∀ j, in777e_color (in777e_anchors j)=j := by
  decide

private lemma in777e_color_overlap :
    ∀ S : Finset (Fin 11), S.card=3 → in777e_stable S →
      2 ≤ (S ∩ in777e_anchors (in777e_color S)).card := by
  unfold in777e_stable
  decide

theorem op_193_eleven_cycle_stable_triples_anchored_seven_coloring :
    ∃ (c : Finset (Fin 11) → Fin 7) (A : Fin 7 → Finset (Fin 11)),
      (∀ j, (A j).card=3 ∧ (∀ i : Fin 11, i∈A j → i+1∉A j) ∧ c (A j)=j) ∧
      (∀ S : Finset (Fin 11), S.card=3 → (∀ i : Fin 11, i∈S → i+1∉S) →
        2 ≤ (S ∩ A (c S)).card) ∧
      ∀ S T : Finset (Fin 11), S.card=3 → T.card=3 →
        (∀ i : Fin 11, i∈S → i+1∉S) → (∀ i : Fin 11, i∈T → i+1∉T) →
        Disjoint S T → c S ≠ c T := by
  refine ⟨in777e_color,in777e_anchors,?_,?_,?_⟩
  · intro j
    exact ⟨(in777e_anchors_good j).1,(in777e_anchors_good j).2,in777e_anchor_color j⟩
  · exact in777e_color_overlap
  · intro S T hS hT hs ht hdis heq
    have h1 := in777e_color_overlap S hS hs
    have h2 := in777e_color_overlap T hT ht
    rw [← heq] at h2
    let A := in777e_anchors (in777e_color S)
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
    have ha := (in777e_anchors_good (in777e_color S)).1
    dsimp [A] at hh
    omega
