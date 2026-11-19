import AFTD.Prelude

/-!
# truncation_k4_double_selected_external

Topic: graphs   Node: 36956f69151a

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The explicit external port colors in a strong six-coloring of the truncation of the complete four-vertex base.
-/

def truncation_k4_double_selected_external : Fin 4 → Fin 6 → Fin 6 :=
  fun _ => ![0,2,4,3,5,1]
