import AFTD.Prelude

/-!
# external_neighbor_count_with_r_internal

Topic: graphs   Node: be592780aa4c

Provenance: helper lemma. OP-1957 variable-shore bridge-family incidence and padded-walk count.

At least r internal neighbors leave at most d−r external neighbors.
-/

theorem external_neighbor_count_with_r_internal
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (q : V) (S C : Finset V) (d r : ℕ) (hSC : Disjoint S C)
    (hmax : (H.neighborFinset q).card ≤ d)
    (hfour : r ≤ ((H.neighborFinset q) ∩ S).card) :
    ((H.neighborFinset q) ∩ C).card + r ≤ d := by
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
