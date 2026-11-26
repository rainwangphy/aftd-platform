import AFTD.Prelude
import AFTD.Kb.Tcs.Op309AffineFiftySixGraph

/-!
# op309_affine_fifty_six_selected

Topic: graphs   Node: 5e7ede971844

Provenance: helper lemma. OP-309 experiments 40692 and 40694.

The twelve vertex-disjoint P3s selected in the 56-vertex example.
-/

def op309_affine_fifty_six_selected [DecidableRel op309_affine_fifty_six_graph.Adj] : Finset op309_affine_fifty_six_graph.edgeSet := Finset.univ.filter fun e => ∃ h : Fin 12,
  e.1 = s(Fin.ofNat 56 (3*h.val), Fin.ofNat 56 (3*h.val+1)) ∨
  e.1 = s(Fin.ofNat 56 (3*h.val+1), Fin.ofNat 56 (3*h.val+2))
