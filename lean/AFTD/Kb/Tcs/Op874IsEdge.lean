import AFTD.Prelude
import AFTD.Kb.Tcs.Op874A
import AFTD.Kb.Tcs.Op874B
import AFTD.Kb.Tcs.Op874Q0
import AFTD.Kb.Tcs.Op874Q1
import AFTD.Kb.Tcs.Op874IsMEdge
import AFTD.Kb.Tcs.Op874V

/-!
# op874IsEdge

Topic: graphs   Node: 570797c44da8

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The edge relation of the chain, as ordered pairs: A 8-cycle, the two B 4-cycles, and the eight matching edge types.
-/

/-- Ordered-pair description of the edge relation: the A 8-cycle, the two B 4-cycles, and the matching edges. -/
def op874IsEdge {k : ℕ} [NeZero k] (u v : op874V k) : Prop := 
  (∃ (i : Fin k) (j : Fin 8), u = op874A i j ∧ v = op874A i (j+1)) ∨
  (∃ (i : Fin k) (j : Fin 4), u = op874B i (op874Q0 j) ∧ v = op874B i (op874Q0 (j+1))) ∨
  (∃ (i : Fin k) (j : Fin 4), u = op874B i (op874Q1 j) ∧ v = op874B i (op874Q1 (j+1))) ∨
  op874IsMEdge u v
