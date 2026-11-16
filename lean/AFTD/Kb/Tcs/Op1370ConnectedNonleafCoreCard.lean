import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370ConnectedNonleafCore

/-!
# op1370_connected_nonleaf_core_card

Topic: combinatorics   Node: b606c22c1b1d

Provenance: helper lemma.

In a connected finite simple graph with at least three vertices, every set containing all vertices of degree at least two induces a connected graph.
-/

open scoped BigOperators

theorem op1370_connected_nonleaf_core_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hV : 3 ≤ Fintype.card V) (S : Finset V)
    (hS : ∀ v, 2 ≤ G.degree v → v ∈ S) : (G.induce (S : Set V)).Connected := by
  classical
  apply op1370_connected_nonleaf_core G hG.preconnected S
  · by_contra hne
    have hd : ∀ v, G.degree v ≤ 1 := by
      intro v
      by_contra hv
      have hlarge : 2 ≤ G.degree v := by omega
      exact hne ⟨v, hS v hlarge⟩
    have hsum : (∑ v : V, G.degree v) ≤ Fintype.card V := by
      calc
        (∑ v : V, G.degree v) ≤ ∑ _v : V, 1 := by
          apply Finset.sum_le_sum
          intro v hv
          exact hd v
        _ = Fintype.card V := by simp
    have hedge : Fintype.card V ≤ G.edgeFinset.card + 1 := by
      rw [G.edgeFinset_card]
      simpa only [Nat.card_eq_fintype_card] using hG.card_vert_le_card_edgeSet_add_one
    have hdegree := G.sum_degrees_eq_twice_card_edges
    omega
  · exact hS
