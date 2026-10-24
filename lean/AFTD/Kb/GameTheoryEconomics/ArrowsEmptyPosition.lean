import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPosition

/-!
# arrows_empty_position

Topic: combinatorial_games   Node: 2b8cbc415c52

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

The empty position in the Game of Arrows on graph G is the position with an empty set of arrows.
-/

/-- The empty position with no marked arrows on a graph G. -/
def arrows_empty_position {V : Type} (G : SimpleGraph V) : ArrowsPosition V G where
  arrows := ∅
  arrows_sub := by simp
  arrows_asymm := by simp
