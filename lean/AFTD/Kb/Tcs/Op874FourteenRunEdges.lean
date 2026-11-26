import AFTD.Prelude

/-!
# op874_fourteen_run_edges

Topic: graphs   Node: 38fd00e5fdb6

Provenance: helper lemma. All-matching maximum-cut palette obstruction for OP-874, using the local criterion in https://arxiv.org/abs/2610.41950.

The fourteen-cycle and seven specified chords of the finite all-matching run obstruction.
-/

def op874_fourteen_run_edges : Finset (Sym2 (Fin 14)) := {s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,6), s(6,7), s(7,8), s(8,9), s(9,10), s(10,11), s(11,12), s(12,13), s(13,0), s(0,5), s(1,10), s(2,7), s(3,12), s(4,9), s(6,11), s(8,13)}
