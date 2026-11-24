import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957ZeroDefectRelaxationForbidden

/-!
# op1957_zero_defect_relaxation_graph

Topic: graphs   Node: 4794225658ee

Provenance: helper lemma. OP-1957: k=9 zero-defect relaxation, experiment 38245.

The graph with all distinct pairs adjacent except the forbidden pairs in either order.
-/

def op1957_zero_defect_relaxation_graph : SimpleGraph (Fin 36) := {
  Adj := fun u v => u ≠ v ∧ ¬ op1957_zero_defect_relaxation_forbidden u v ∧ ¬ op1957_zero_defect_relaxation_forbidden v u
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩ }
