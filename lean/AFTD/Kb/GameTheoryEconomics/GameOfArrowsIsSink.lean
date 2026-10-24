import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPosition

/-!
# game_of_arrows_is_sink

Topic: combinatorial_games   Node: 3cc650c246b3

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

In a position P of the Game of Arrows on graph G, a vertex v is a sink if v has at least one incident edge and every incident edge points toward v.
-/

/-- A vertex v is a sink in position P of the Game of Arrows if it has degree at least 1 and all incident edges point to v. -/
def game_of_arrows_is_sink {V : Type} (G : SimpleGraph V) (P : ArrowsPosition V G) (v : V) : Prop := (∃ u, G.Adj u v) ∧ ∀ u, G.Adj u v → (u, v) ∈ P.arrows
