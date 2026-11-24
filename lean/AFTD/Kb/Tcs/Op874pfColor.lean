import AFTD.Prelude

/-!
# op874pf_color

Topic: graphs   Node: 08dc36a4f1d7

Provenance: helper lemma. OP-874: explicit fixed-external-color obstruction.

The explicit six-color assignment to the edges of the eight-vertex obstruction.
-/

def op874pf_color (e : Sym2 (Fin 8)) : Fin 6 := if e=s(0,1) then 2 else if e=s(0,3) then 5 else if e=s(0,5) then 1 else
  if e=s(1,2) then 3 else if e=s(1,7) then 1 else if e=s(2,3) then 2 else
  if e=s(2,6) then 0 else if e=s(3,4) then 0 else if e=s(4,5) then 5 else
  if e=s(4,7) then 4 else if e=s(5,6) then 4 else if e=s(6,7) then 3 else 0
