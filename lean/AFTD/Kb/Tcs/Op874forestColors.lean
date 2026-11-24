import AFTD.Prelude

/-!
# op874forest_colors

Topic: graphs   Node: d8875bcf378a

Provenance: helper lemma. OP-874: ten-vertex forest fixed-color obstruction, experiments 38417–38419.

The fixed external colors of the ten-vertex forest obstruction.
-/

def op874forest_colors : Fin 15 → Fin 6 := ![5,4,1,3,0,2,1,0,4,0,3,2,5,4,2]
