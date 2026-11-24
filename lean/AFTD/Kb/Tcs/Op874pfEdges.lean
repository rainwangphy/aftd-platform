import AFTD.Prelude

/-!
# op874pf_edges

Topic: graphs   Node: 836b3c3abdca

Provenance: helper lemma. OP-874: finite pair-rich pseudoforest port obstruction, experiment 38406.

The twelve edges of the explicit eight-vertex port-obstruction graph.
-/

def op874pf_edges : Finset (Sym2 (Fin 8)) := {s(0,1),s(0,3),s(0,5),s(1,2),s(1,7),s(2,3),
   s(2,6),s(3,4),s(4,5),s(4,7),s(5,6),s(6,7)}
