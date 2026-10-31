import AFTD.Prelude
import AFTD.Kb.Tcs.Die
import AFTD.Kb.Tcs.BeatScore
import AFTD.Kb.Tcs.MinimalAdvantage

/-!
# dice_graph

Topic: combinatorics   Node: 082bb3440ec8

Provenance: formalization of a published result. Source: arXiv:2610.40321 Sec 2

For an explicit parameter n : ℕ, dice_graph n is the bundled Digraph on Die n whose adjacency relation Adj x y holds if and only if beat_score x y = minimal_advantage n.
-/

/-- Bundled Digraph on Die n with edges defined by minimal winning advantage. -/
def dice_graph (n : ℕ) : Digraph (Die n) where Adj x y := beat_score x y = minimal_advantage n
