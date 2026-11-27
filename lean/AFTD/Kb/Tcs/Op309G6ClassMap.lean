import AFTD.Prelude

/-!
# op309_g6_class_map

Topic: graphs   Node: 508c35daf10b

Provenance: helper lemma. step towards op309_girth6_source_forest_clique5_nonfive_example

Explicit class map sending each of the 30 outside edges of the selected P3 forest to one of 8 classes: the table is (0,34)|->4, (1,18)|->1, (1,29)|->2, (2,7)|->2, (2,10)|->1, (3,32)|->0, (4,23)|->2, (4,28)|->3, (5,17)|->2, (5,20)|->3, (6,13)|->1, (7,21)|->7, (8,16)|->2, (8,30)|->7, (9,31)|->6, (10,14)|->2, (11,16)|->1, (11,28)|->2, (12,26)|->5, (13,19)|->2, (14,17)|->1, (15,34)|->0, (19,23)|->3, (20,26)|->2, (22,25)|->2, (22,29)|->3, (24,32)|->6, (25,33)|->5, (27,35)|->4, (31,35)|->0.
-/

/-- Class label in Fin 8 for each of the 30 outside edges of the selected forest; unlisted edges get label 0. -/
def op309_g6_class_map : Sym2 (Fin 36) → Fin 8 := fun e =>
  if e = s(0, 34) then 4 else if e = s(1, 18) then 1 else if e = s(1, 29) then 2
  else if e = s(2, 7) then 2 else if e = s(2, 10) then 1 else if e = s(3, 32) then 0
  else if e = s(4, 23) then 2 else if e = s(4, 28) then 3 else if e = s(5, 17) then 2
  else if e = s(5, 20) then 3 else if e = s(6, 13) then 1 else if e = s(7, 21) then 7
  else if e = s(8, 16) then 2 else if e = s(8, 30) then 7 else if e = s(9, 31) then 6
  else if e = s(10, 14) then 2 else if e = s(11, 16) then 1 else if e = s(11, 28) then 2
  else if e = s(12, 26) then 5 else if e = s(13, 19) then 2 else if e = s(14, 17) then 1
  else if e = s(15, 34) then 0 else if e = s(19, 23) then 3 else if e = s(20, 26) then 2
  else if e = s(22, 25) then 2 else if e = s(22, 29) then 3 else if e = s(24, 32) then 6
  else if e = s(25, 33) then 5 else if e = s(27, 35) then 4 else if e = s(31, 35) then 0
  else 0
