import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPosition
import AFTD.Kb.GameTheoryEconomics.GameOfArrowsIsSink
import AFTD.Kb.GameTheoryEconomics.GameOfArrowsIsSource

/-!
# game_of_arrows_legal_move

Topic: combinatorial_games   Node: b33c0d8d6ce5

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

A move from position P to Q in the Game of Arrows on graph G is legal if an unmarked edge between adjacent vertices u and v is oriented as (u, v) in Q, and neither u nor v is a sink or source in Q.
-/

/-- A transition from position P to Q in the Game of Arrows is a legal move if Q adds an oriented edge without making either endpoint a sink or source. -/
def game_of_arrows_legal_move {V : Type} [DecidableEq V] (G : SimpleGraph V) (P Q : ArrowsPosition V G) : Prop := ∃ (u v : V), G.Adj u v ∧ (u, v) ∉ P.arrows ∧ (v, u) ∉ P.arrows ∧
    Q.arrows = insert (u, v) P.arrows ∧
    ¬ game_of_arrows_is_sink G Q u ∧ ¬ game_of_arrows_is_source G Q u ∧
    ¬ game_of_arrows_is_sink G Q v ∧ ¬ game_of_arrows_is_source G Q v
