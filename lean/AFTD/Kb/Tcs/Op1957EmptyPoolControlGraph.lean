import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957EmptyPoolControlForbidden

/-!
# op1957_empty_pool_control_graph

Topic: graphs   Node: 0fabcf0467e1

Provenance: helper lemma. OP-1957; explicit exceptional empty-pool controls, experiments 41527, 41538 and 41541.

The graph on 28 vertices obtained by excluding the displayed ordered forbidden pairs in both directions.
-/

def op1957_empty_pool_control_graph (z : Fin 28) : SimpleGraph (Fin 28) := {
  Adj := fun u v => u ≠ v ∧ ¬ op1957_empty_pool_control_forbidden z u v ∧ ¬ op1957_empty_pool_control_forbidden z v u
  symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩
}
