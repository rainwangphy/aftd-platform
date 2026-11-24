import AFTD.Prelude

/-!
# op874pft_ends

Topic: graphs   Node: 6aa0d4e5a421

Provenance: helper lemma. OP-874: explicit eight-vertex fixed-color obstruction.

The indexed endpoints of the twelve edges in the eight-vertex obstruction.
-/

def op874pft_ends : Fin 12 → Sym2 (Fin 8) := ![s(0,1),s(0,3),s(0,5),s(1,2),s(1,7),s(2,3),
    s(2,6),s(3,4),s(4,5),s(4,7),s(5,6),s(6,7)]
