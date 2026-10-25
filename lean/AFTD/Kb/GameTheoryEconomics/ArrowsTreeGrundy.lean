import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos
import AFTD.Kb.GameTheoryEconomics.ArrowsEmptyPos
import AFTD.Kb.GameTheoryEconomics.ArrowsPosGrundy

/-!
# arrows_tree_grundy

Topic: combinatorial_games   Node: 1f1be75816bc

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

The Grundy value of the Game of Arrows on a finite simple graph G is the Grundy value of the empty position ArrowsEmptyPos V at fuel (Fintype.card V * Fintype.card V).
-/

/-- The Grundy value of the empty position of the Game of Arrows on a finite graph G. -/
noncomputable def arrows_tree_grundy {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := arrows_pos_grundy G (Fintype.card V * Fintype.card V) (ArrowsEmptyPos V)
