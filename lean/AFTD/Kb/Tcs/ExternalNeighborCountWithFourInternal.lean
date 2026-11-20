import AFTD.Prelude

/-!
# external_neighbor_count_with_four_internal

Topic: graphs   Node: cea3b414fc30

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family, without the first zero-codegree witness.

Four internal neighbors leave at most d−4 external neighbors.
-/

theorem external_neighbor_count_with_four_internal
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (q : V) (S C : Finset V) (d : ℕ) (hSC : Disjoint S C)
    (hmax : (H.neighborFinset q).card ≤ d)
    (hfour : 4 ≤ ((H.neighborFinset q) ∩ S).card) :
    ((H.neighborFinset q) ∩ C).card + 4 ≤ d := by
  classical
  let A := (H.neighborFinset q) ∩ S
  let B := (H.neighborFinset q) ∩ C
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hsub : A ∪ B ⊆ H.neighborFinset q := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Finset.mem_inter.mp ha).1
    · exact (Finset.mem_inter.mp ha).1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hc
  have hc' := le_trans hc hmax
  dsimp [A,B] at hc'
  omega
