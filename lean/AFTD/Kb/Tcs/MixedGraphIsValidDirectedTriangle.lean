import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphIsValid

/-!
# mixed_graph_is_valid_directed_triangle

Topic: graphs   Node: 50beebf1552a

Provenance: helper lemma. Sanity lemma for mixed graphs, arXiv:2610.14110 (New mixed cages, bounds and computational results).

Sanity check: the directed triangle is a mixed graph (no loops, no antiparallel arcs).
-/

theorem mixed_graph_is_valid_directed_triangle :
    mixed_graph_is_valid (⊥ : SimpleGraph (Fin 3)) (fun x y => y = x + 1) := by
  refine ⟨by decide, by decide, fun _ _ h => h.elim⟩
