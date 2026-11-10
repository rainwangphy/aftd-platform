import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPairStableSupportMaxIncidenceTwoBadPackingCounterexample
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_pair_stable_k4_link_two_attachment_sharp

Topic: graphs   Node: 072789711618

Provenance: helper lemma. The already certified eight-vertex pair-stable graph supplies a sharpness example for the K4 link-extension lemma.

A two-edge-stable graph can contain a four-clique and a distinguished clique vertex for which one face vertex has no external common neighbor with the distinguished vertex.
-/

open scoped Sym2

theorem simple_graph_pair_stable_k4_link_two_attachment_sharp : ∃ (G : SimpleGraph (Fin 8)) (x a b c : Fin 8),
    (∀ e f : Sym2 (Fin 8), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
      simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) ∧
    G.IsNClique 4 ({x,a,b,c} : Finset (Fin 8)) ∧
    (∀ y : Fin 8, y ∉ ({x,a,b,c} : Finset (Fin 8)) → G.Adj x y → ¬ G.Adj c y) := by
  refine ⟨In701CE.G,0,2,7,4,In701CE.stable,?_,?_⟩
  · decide +kernel
  · decide +kernel
