import AFTD.Prelude

/-!
# BoxPattern

Topic: combinatorics   Node: 2ce6b31521f7

Provenance: helper lemma. step towards grid_box_free_max_five_seven

A coloured rectangle pattern in an $a\times b$ grid: a pair of rows $x_1<x_2$, a pair of columns $y_1<y_2$, and a colour, encoded as the tuple $(x_1,x_2,y_1,y_2,\text{col})$.
-/

/-- Coloured $2\times 2$ rectangle pattern of an $a\times b$ grid: rows $(x_1,x_2)$, columns $(y_1,y_2)$, colour. -/
abbrev BoxPattern (a b : ℕ) : Type := Fin a × Fin a × Fin b × Fin b × Bool
