import AFTD.Prelude

/-!
# op874pf_missing

Topic: graphs   Node: e7c8cc7d112f

Provenance: helper lemma. OP-874: finite pair-rich pseudoforest port obstruction, experiment 38406.

The three missing colors assigned to each vertex in the explicit eight-vertex port-obstruction graph.
-/

def op874pf_missing : Fin 8 → Finset (Fin 6) := ![{0,3,4},{0,4,5},{1,4,5},{1,3,4},
    {1,2,3},{0,2,3},{1,2,5},{0,2,5}]
