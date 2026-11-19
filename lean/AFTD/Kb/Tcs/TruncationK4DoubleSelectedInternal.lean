import AFTD.Prelude

/-!
# truncation_k4_double_selected_internal

Topic: graphs   Node: a2efaea85b58

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The explicit internal port colors in a strong six-coloring of the truncation of the complete four-vertex base.
-/

def truncation_k4_double_selected_internal : Fin 4 → Fin 6 → Fin 6 :=
  ![![1,5,3,0,0,0], ![1,0,0,4,2,0],
    ![0,5,0,4,0,0], ![0,0,3,0,2,0]]
