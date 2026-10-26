import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPieceThread
import AFTD.Kb.GameTheoryEconomics.IsTreeSpecial

/-!
# is_internal_piece_thread

Topic: combinatorial_games   Node: 41efafee6f18

Provenance: formalization of a published result. Source: arXiv:2610.15145, Question 11.4

An internal thread of a piece of a tree T is a piece thread whose endpoints both have degree at least 3 in T and are not special.
-/

/-- An internal thread of a piece is a thread whose endpoints both have degree at least 3 in the piece. -/
def is_internal_piece_thread {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {u v : V} (p : T.Walk u v) : Prop := is_piece_thread T p ∧ 3 ≤ T.degree u ∧ ¬ is_tree_special T u ∧ 3 ≤ T.degree v ∧ ¬ is_tree_special T v
