import AFTD.Prelude

/-!
# op1370_connected_nonleaf_core

Topic: combinatorics   Node: 85024dfd624e

Provenance: helper lemma.

In a finite preconnected graph, any nonempty vertex set containing every vertex of degree at least two induces a connected subgraph.
-/

theorem op1370_connected_nonleaf_core
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Preconnected) (S : Finset V) (hne : S.Nonempty)
    (hS : ∀ v, 2 ≤ G.degree v → v ∈ S) : (G.induce (S : Set V)).Connected := by
  classical
  have hs : ∀ v ∉ (S : Set V), (G.neighborSet v).Subsingleton := by
    intro v hv
    have hn : ¬ 2 ≤ G.degree v := fun h => hv (hS v h)
    have hd : G.degree v ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hn)
    have hc : (G.neighborFinset v).card ≤ 1 := hd
    simpa only [SimpleGraph.coe_neighborFinset] using (Finset.card_le_one_iff_subsingleton.mp hc)
  obtain ⟨v, hv⟩ := hne
  letI : Nonempty (S : Set V) := ⟨⟨v, hv⟩⟩
  exact ⟨hG.induce_of_degree_eq_one hs⟩
