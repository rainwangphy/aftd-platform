import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphHasGirth
import AFTD.Kb.Tcs.MixedGraphHasCycleDirectedTriangle
import AFTD.Kb.Tcs.MixedGraphHasCycle

/-!
# mixed_graph_has_girth_directed_triangle

Topic: graphs   Node: c5cd3f98bf3c

Provenance: helper lemma. Sanity lemma for mixed-graph girth, arXiv:2610.14110 (New mixed cages, bounds and computational results).

Sanity check: the directed triangle has girth 3.
-/

theorem mixed_graph_has_girth_directed_triangle :
    mixed_graph_has_girth (⊥ : SimpleGraph (Fin 3)) (fun x y => y = x + 1) 3 :=
  ⟨mixed_graph_has_cycle_directed_triangle, fun _ ht h => by have := h.1; omega⟩
