import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957BarrierCountExampleForbidden

/-!
# op1957_barrier_count_example_graph

Topic: graphs   Node: 7adadd19177d

Provenance: helper lemma. OP-1957; explicit graph from the saturated barrier count model, experiments 39772, 39775 and 39778.

The simple graph on 44 vertices whose edges are the distinct pairs that are forbidden in neither order.
-/

def op1957_barrier_count_example_graph : SimpleGraph (Fin 44) := {
  Adj := fun u v => u ≠ v ∧ ¬ op1957_barrier_count_example_forbidden u v ∧ ¬ op1957_barrier_count_example_forbidden v u
  symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩
}
