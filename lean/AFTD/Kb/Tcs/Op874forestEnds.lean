import AFTD.Prelude

/-!
# op874forest_ends

Topic: graphs   Node: 7a82c11e95b6

Provenance: helper lemma. OP-874: ten-vertex forest fixed-color obstruction, experiments 38417–38419.

The fifteen indexed edges of the ten-vertex forest obstruction.
-/

def op874forest_ends : Fin 15 → Sym2 (Fin 10) :=
  ![s(0,1),s(0,3),s(0,9),s(1,2),s(1,8),s(2,3),s(2,5),s(3,7),
    s(4,5),s(4,6),s(4,9),s(5,6),s(6,7),s(7,8),s(8,9)]
