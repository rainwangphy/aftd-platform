import AFTD.Prelude
import AFTD.Kb.Tcs.MaxDegreeInduceV3LeTwoIffNeighborFilter
import AFTD.Kb.Tcs.SimpleGraphV3

/-!
# subcubic_induce_V3_le_two_induce_subset

Topic: graphs   Node: cd4552f4f5dc

Provenance: helper lemma. step towards subcubic_maxDegree_induce_V3_le_two_exists_rich_neighbor_five_coloring

If the finite simple graph G has maximum degree at most 3 and Delta(G[V_3]) <= 2, then for every vertex subset S the induced subgraph G[S] has maximum degree at most 3 and Delta(G[S][V_3(G[S])]) <= 2.
-/

/-- Heredity of both hypotheses along an induced subgraph on an arbitrary vertex subset (note: the vertex type changes to the subtype). -/
theorem subcubic_induce_V3_le_two_induce_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)]
    (hdeg : G.maxDegree ≤ 3)
    (h3 : (G.induce (simple_graph_V3 G : Set V)).maxDegree ≤ 2) :
    (G.induce S).maxDegree ≤ 3 ∧
      ((G.induce S).induce (simple_graph_V3 (G.induce S) : Set S)).maxDegree ≤ 2 := by
  let H := G.induce S
  have h_deg_le : ∀ u : S, H.degree u ≤ G.degree u.val :=
    fun u => SimpleGraph.Copy.degree_le (SimpleGraph.Embedding.induce S (G := G)).toCopy u
  have h_max : H.maxDegree ≤ 3 :=
    (SimpleGraph.Copy.maxDegree_mono (SimpleGraph.Embedding.induce S (G := G)).toCopy).trans hdeg
  refine ⟨h_max, ?_⟩
  rw [maxDegree_induce_V3_le_two_iff_neighbor_filter H]
  have h3' := (maxDegree_induce_V3_le_two_iff_neighbor_filter G).mp h3
  intro v hv
  have hGv : G.degree v.val = 3 := by
    apply le_antisymm
    · exact (G.degree_le_maxDegree v.val).trans hdeg
    · rw [← hv]
      exact h_deg_le v
  have h_maps : Set.MapsTo (Subtype.val : S → V)
      (((H.neighborFinset v).filter (fun w => H.degree w = 3) : Finset S) : Set S)
      (((G.neighborFinset v.val).filter (fun w => G.degree w = 3) : Finset V) : Set V) := by
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw ⊢
    refine ⟨?_, ?_⟩
    · exact hw.1
    · apply le_antisymm
      · exact (G.degree_le_maxDegree w.val).trans hdeg
      · rw [← hw.2]
        exact h_deg_le w
  have h_inj : Set.InjOn Subtype.val (((H.neighborFinset v).filter (fun w => H.degree w = 3) : Finset S) : Set S) :=
    Subtype.val_injective.injOn
  have h_le := Finset.card_le_card_of_injOn Subtype.val h_maps h_inj
  exact h_le.trans (h3' v.val hGv)
