import AFTD.Prelude
import AFTD.Kb.Tcs.DiagramSlidingTree
import AFTD.Kb.Tcs.TerminalBoxes
import AFTD.Kb.Tcs.IsStandardYoungTableauList
import AFTD.Kb.Tcs.ListDescentAt

/-!
# diagram_slide_expansion_agrees_with_descents

Topic: combinatorics   Node: a33f032114ad

Provenance: formalization of a published result. Source: arXiv:2611.07715, Proposition 4.15

A sliding tree `t` on a finite diagram $D$ satisfies `diagram_slide_expansion_agrees_with_descents D t` if for every list $l$ representing a standard Young tableau on $D$ (`is_standard_young_tableau_list D l`) and every index $k$, the terminal list of cells `terminal_boxes t l` has a row descent at $k$ (`list_descent_at (terminal_boxes t l) k`) if and only if $l$ has a row descent at $k$ (`list_descent_at l k`).
-/

/-- A sliding tree agrees with descents if for every standard tableau on D, the terminal word descents match the tableau descents. -/
def diagram_slide_expansion_agrees_with_descents (D : Finset (ℕ × ℕ)) (t : DiagramSlidingTree D) : Prop := ∀ l, is_standard_young_tableau_list D l → ∀ k, list_descent_at (terminal_boxes t l) k ↔ list_descent_at l k
