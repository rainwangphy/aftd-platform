import AFTD.Prelude

/-!
# f4_adj_bool

Topic: graphs   Node: 3eb344ce2bc3

Provenance: helper lemma. step towards op1917_exists_nonregular_resistance_regular_order_16

Boolean adjacency predicate for the 16-vertex graph F(4) from arXiv:2611.21670.
-/

/-- Boolean adjacency predicate for the 16-vertex graph F(4) from arXiv:2611.21670. -/
def f4_adj_bool (i j : Fin 16) : Bool :=
  let u := i.val
  let v := j.val
  if u == v then false
  else
    let e1 := (u < 4 && v < 4) || (4 ≤ u && u < 8 && 4 ≤ v && v < 8)
    let e2 := (u < 4 && 8 ≤ v && v < 12) || (v < 4 && 8 ≤ u && u < 12) ||
              (4 ≤ u && u < 8 && 12 ≤ v && v < 16) || (4 ≤ v && v < 8 && 12 ≤ u && u < 16)
    let y0 := (u == 8 || u == 9 || u == 12 || u == 13) && (v == 8 || v == 9 || v == 12 || v == 13)
    let y0_non := (u == 8 && v == 12) || (u == 12 && v == 8) || (u == 9 && v == 13) || (u == 13 && v == 9)
    let e3_0 := y0 && !y0_non
    let y1 := (u == 10 || u == 11 || u == 14 || u == 15) && (v == 10 || v == 11 || v == 14 || v == 15)
    let y1_non := (u == 10 && v == 14) || (u == 14 && v == 10) || (u == 11 && v == 15) || (u == 15 && v == 11)
    let e3_1 := y1 && !y1_non
    e1 || e2 || e3_0 || e3_1
