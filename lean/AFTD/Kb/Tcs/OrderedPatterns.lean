import AFTD.Prelude
import AFTD.Kb.Tcs.BoxPattern

/-!
# ordered_patterns

Topic: combinatorics   Node: 8287ca21f57a

Provenance: helper lemma. step towards grid_box_free_max_five_seven

The finite set of ordered coloured rectangle patterns of an $a\times b$ grid, i.e. the patterns with $x_1<x_2$ and $y_1<y_2$. Its cardinality is $2\binom a2\binom b2$, the number of "coloured rectangle slots".
-/

/-- All ordered coloured rectangle slots of an $a\times b$ grid. -/
def ordered_patterns (a b : ℕ) : Finset (BoxPattern a b) := Finset.univ.filter (fun p => p.1 < p.2.1 ∧ p.2.2.1 < p.2.2.2.1)
