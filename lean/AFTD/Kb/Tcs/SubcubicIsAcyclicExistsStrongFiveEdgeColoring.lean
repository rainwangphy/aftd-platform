import AFTD.Prelude
import AFTD.Kb.Tcs.SubcubicIsAcyclicExistsLeafEdgeDistTwoLeFour
import AFTD.Kb.Tcs.SimpleGraphStrongFiveEdgeColoringExtendLeafOfNcard
import AFTD.Kb.Tcs.MaxDegreeLeTwoExistsRichNeighborFiveColoring
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# subcubic_isAcyclic_exists_strong_five_edge_coloring

Topic: graphs   Node: 3ebc91a54ab6

Provenance: helper lemma. step towards subcubic_isAcyclic_exists_rich_neighbor_five_coloring

Every finite simple graph of maximum degree at most 3 that is acyclic admits a strong 5-edge-coloring (where all edges are rich).
-/

/-- Every subcubic finite acyclic simple graph admits a strong 5-edge-coloring. -/
theorem subcubic_isAcyclic_exists_strong_five_edge_coloring {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : G.maxDegree ≤ 3) (hforest : G.IsAcyclic) :
    ∃ c : G.lineGraph.Coloring (Fin 5), ∀ e, simple_graph_edge_is_rich G c e := by
  classical
  generalize hn : G.edgeFinset.card = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hne : G.edgeFinset.Nonempty
    · obtain ⟨e, v, hv, hleaf, hfour⟩ :=
        subcubic_isAcyclic_exists_leaf_edge_dist_two_le_four G hdeg hforest hne
      have hcard : (G.deleteEdges {e.val}).edgeFinset.card < n := by
        have he : e.val ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr e.property
        have hfin : (G.deleteEdges {e.val}).edgeFinset = G.edgeFinset.erase e.val := by
          ext f
          simp [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, and_comm]
        rw [hfin, Finset.card_erase_of_mem he]
        have hpos := Finset.card_pos.mpr hne
        omega
      have hsub := G.deleteEdges_le {e.val}
      have hsmall := ih _ hcard (G.deleteEdges {e.val})
        ((SimpleGraph.maxDegree_mono hsub).trans hdeg)
        (hforest.anti hsub) rfl
      apply simple_graph_strong_five_edge_coloring_extend_leaf_of_ncard G e v hv hleaf _ hsmall
      have hset : {f : G.edgeSet | f ≠ e ∧ (G.lineGraph.Adj e f ∨
          ∃ g : G.edgeSet, G.lineGraph.Adj g e ∧ G.lineGraph.Adj g f)} =
          (↑((Finset.univ.erase e).filter (fun f : G.edgeSet =>
            G.lineGraph.Adj e f ∨ ∃ g : G.edgeSet,
              G.lineGraph.Adj g e ∧ G.lineGraph.Adj g f)) : Set G.edgeSet) := by
        ext f
        simp
      rw [hset, Set.ncard_coe_finset]
      exact hfour
    · have hempty : IsEmpty G.edgeSet := by
        refine ⟨fun e => hne ⟨e.val, SimpleGraph.mem_edgeFinset.mpr e.property⟩⟩
      letI := hempty
      refine ⟨{ toFun := fun e => isEmptyElim e, map_rel' := fun {e} => isEmptyElim e }, ?_⟩
      exact fun e => isEmptyElim e
