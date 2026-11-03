import AFTD.Prelude

/-!
# digraph_local_four_witness

Topic: graphs   Node: 5ebe2c894270

Provenance: helper lemma. arXiv:2601.11847, Problem 5.2 and Proposition 2.3; a local-obstruction construction used in the OP-337 campaign.

A 24-vertex oriented digraph specified by its out-neighborhoods: an eight-vertex two-outregular core with two private sink leaves at each core vertex.
-/

def digraph_local_four_witness (v : Fin 24) : Finset (Fin 24) :=
  if v = 0 then {4,5,8,9} else
  if v = 1 then {3,7,10,11} else
  if v = 2 then {0,6,12,13} else
  if v = 3 then {2,4,14,15} else
  if v = 4 then {2,7,16,17} else
  if v = 5 then {1,6,18,19} else
  if v = 6 then {0,1,20,21} else
  if v = 7 then {3,5,22,23} else ∅
