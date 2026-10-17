import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphHasCycle

/-!
# mixed_graph_has_cycle_directed_triangle

Topic: graphs   Node: 0a1b09444e55

Provenance: helper lemma. Sanity lemma for mixed-graph cycles, arXiv:2610.14110 (New mixed cages, bounds and computational results).

Sanity check: the directed triangle 0 → 1 → 2 → 0 has a 3-cycle.
-/

theorem mixed_graph_has_cycle_directed_triangle :
    mixed_graph_has_cycle (⊥ : SimpleGraph (Fin 3)) (fun x y => y = x + 1) 3 :=
  ⟨le_rfl, id, Function.injective_id, fun i => Or.inr (finRotate_apply i)⟩
