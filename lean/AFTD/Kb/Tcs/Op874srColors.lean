import AFTD.Prelude

/-!
# op874sr_colors

Topic: graphs   Node: 539c240dff7e

Provenance: helper lemma. OP-874: single-edge repair obstruction, experiments 38435 and 38438.

The fixed external colors of the single-recolor obstruction.
-/

def op874sr_colors : Fin 12 → Fin 6 := ![4,3,0,3,1,4,0,5,1,3,4,5]
