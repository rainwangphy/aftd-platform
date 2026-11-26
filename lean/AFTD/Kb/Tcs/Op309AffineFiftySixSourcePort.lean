import AFTD.Prelude
import AFTD.Kb.Tcs.Op309AffineFiftySixGraph

/-!
# op309_affine_fifty_six_source_port

Topic: graphs   Node: f799ea3e04c7

Provenance: helper lemma. OP-309 affine-incidence obstruction, experiment 40694.

A boundary edge from one of the first nine selected P3s to a source uncovered terminal.
-/

def op309_affine_fifty_six_source_port (h : Fin 9) (e : op309_affine_fifty_six_graph.edgeSet) : Prop := ∃ u : Fin 56, 36 ≤ u.val ∧ u.val < 48 ∧
  (e.1 = s(Fin.ofNat 56 (3*h.val),u) ∨ e.1 = s(Fin.ofNat 56 (3*h.val+2),u))
