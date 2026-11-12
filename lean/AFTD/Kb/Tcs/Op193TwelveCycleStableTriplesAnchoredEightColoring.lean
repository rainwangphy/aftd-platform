import AFTD.Prelude

/-!
# op_193_twelve_cycle_stable_triples_anchored_eight_coloring

Topic: graphs   Node: e44b11006564

Provenance: helper lemma. Finite obstruction to the nonanchored-class method; experiment 23343.

The stable triples of the twelve-cycle admit a proper eight-coloring in which each color class has an anchor meeting every triple in that class in at least two vertices.
-/

open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

private def in777t_anchors : Fin 8 → Finset (Fin 12) :=
  ![{0,4,8}, {0,5,9}, {1,4,9}, {1,5,8}, {2,6,10}, {2,7,11}, {3,6,11}, {3,7,10}]

private def in777t_stable (S : Finset (Fin 12)) : Prop :=
  ∀ i : Fin 12, i ∈ S → i+1 ∉ S

lemma in777t_anchors_good :
    ∀ j, (in777t_anchors j).card=3 ∧ in777t_stable (in777t_anchors j) := by
  unfold in777t_stable
  decide

lemma in777t_anchored_cover :
    ∀ S : Finset (Fin 12), S.card=3 → in777t_stable S →
      ∃ j : Fin 8, 2 ≤ (S ∩ in777t_anchors j).card := by
  unfold in777t_stable
  decide


private def in777t_color (S : Finset (Fin 12)) : Fin 8 :=
  if S = in777t_anchors 0 then 0 else
  if S = in777t_anchors 1 then 1 else
  if S = in777t_anchors 2 then 2 else
  if S = in777t_anchors 3 then 3 else
  if S = in777t_anchors 4 then 4 else
  if S = in777t_anchors 5 then 5 else
  if S = in777t_anchors 6 then 6 else
  if S = in777t_anchors 7 then 7 else
  if 2 ≤ (S ∩ in777t_anchors 0).card then 0 else
  if 2 ≤ (S ∩ in777t_anchors 1).card then 1 else
  if 2 ≤ (S ∩ in777t_anchors 2).card then 2 else
  if 2 ≤ (S ∩ in777t_anchors 3).card then 3 else
  if 2 ≤ (S ∩ in777t_anchors 4).card then 4 else
  if 2 ≤ (S ∩ in777t_anchors 5).card then 5 else
  if 2 ≤ (S ∩ in777t_anchors 6).card then 6 else
  7

private lemma in777t_anchor_color : ∀ j, in777t_color (in777t_anchors j)=j := by
  decide

private lemma in777t_color_overlap :
    ∀ S : Finset (Fin 12), S.card=3 → in777t_stable S →
      2 ≤ (S ∩ in777t_anchors (in777t_color S)).card := by
  unfold in777t_stable
  decide

theorem op_193_twelve_cycle_stable_triples_anchored_eight_coloring :
    ∃ (c : Finset (Fin 12) → Fin 8) (A : Fin 8 → Finset (Fin 12)),
      (∀ j, (A j).card=3 ∧ (∀ i : Fin 12, i∈A j → i+1∉A j) ∧ c (A j)=j) ∧
      (∀ S : Finset (Fin 12), S.card=3 → (∀ i : Fin 12, i∈S → i+1∉S) →
        2 ≤ (S ∩ A (c S)).card) ∧
      ∀ S T : Finset (Fin 12), S.card=3 → T.card=3 →
        (∀ i : Fin 12, i∈S → i+1∉S) → (∀ i : Fin 12, i∈T → i+1∉T) →
        Disjoint S T → c S ≠ c T := by
  refine ⟨in777t_color,in777t_anchors,?_,?_,?_⟩
  · intro j
    exact ⟨(in777t_anchors_good j).1,(in777t_anchors_good j).2,in777t_anchor_color j⟩
  · exact in777t_color_overlap
  · intro S T hS hT hs ht hdis heq
    have h1 := in777t_color_overlap S hS hs
    have h2 := in777t_color_overlap T hT ht
    rw [← heq] at h2
    let A := in777t_anchors (in777t_color S)
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
    have ha := (in777t_anchors_good (in777t_color S)).1
    dsimp [A] at hh
    omega
