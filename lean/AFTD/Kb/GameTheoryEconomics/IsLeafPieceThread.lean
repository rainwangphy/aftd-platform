import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPieceThread
import AFTD.Kb.GameTheoryEconomics.IsTreeSpecial

/-!
# is_leaf_piece_thread

Topic: combinatorial_games   Node: 8190e9b76989

Provenance: formalization of a published result. Source: arXiv:2610.15145, Question 11.4

A leaf thread of a piece of a tree T is a piece thread at least one of whose endpoints is a special vertex of T.
-/

/-- A leaf thread of a piece is a thread at least one of whose endpoints is a leaf of the piece. -/
def is_leaf_piece_thread {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {u v : V} (p : T.Walk u v) : Prop := is_piece_thread T p ∧ (is_tree_special T u ∨ is_tree_special T v)
