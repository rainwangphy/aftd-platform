import AFTD.Prelude

/-!
# op874sr_ends

Topic: graphs   Node: 6ce2fa775df3

Provenance: helper lemma. OP-874: single-edge repair obstruction, experiments 38435 and 38438.

The twelve indexed edges of the single-recolor obstruction.
-/

def op874sr_ends : Fin 12 → Sym2 (Fin 8) :=
  ![s(0,1),s(0,4),s(0,6),s(1,2),s(1,4),s(2,3),
    s(2,7),s(3,4),s(3,5),s(5,6),s(5,7),s(6,7)]
