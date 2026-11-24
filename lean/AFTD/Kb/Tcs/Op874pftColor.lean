import AFTD.Prelude

/-!
# op874pft_color

Topic: graphs   Node: 33ba9695be69

Provenance: helper lemma. OP-874: explicit eight-vertex fixed-color obstruction.

The fixed six-color assignment to the twelve indexed obstruction edges.
-/

def op874pft_color : Fin 12 → Fin 6 := ![2,5,1,3,1,2,0,0,5,4,4,3]
