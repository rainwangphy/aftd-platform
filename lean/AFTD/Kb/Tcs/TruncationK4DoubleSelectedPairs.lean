import AFTD.Prelude

/-!
# truncation_k4_double_selected_pairs

Topic: graphs   Node: 15d2ac0ce244

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The six ordered endpoint pairs for the complete graph on four vertices, in the order 01,02,03,12,13,23.
-/

def truncation_k4_double_selected_pairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]
