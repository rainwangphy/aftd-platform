import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos
import AFTD.Kb.GameTheoryEconomics.ArrowsUnmarked
import AFTD.Kb.GameTheoryEconomics.ArrowsIsSink
import AFTD.Kb.GameTheoryEconomics.ArrowsIsSource

/-!
# ArrowsLegalMove

Topic: combinatorial_games   Node: 26f812104de9

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

In a simple graph G, a transition from position p to q in ArrowsPos V is a legal move if there exist u, v with ArrowsUnmarked G p u v such that q.1 is obtained by updating p.1 to true at (u, v), and neither u nor v is a sink or a source in q.
-/

/-- A move from position p to position q is legal if an unmarked edge uv is oriented as u -> v and neither endpoint becomes a sink or source in q. -/
def ArrowsLegalMove {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ArrowsPos V) : Prop := ∃ u v, ArrowsUnmarked G p u v ∧
    (∀ x y, q.1 x y = if x = u ∧ y = v then true else p.1 x y) ∧
    ¬ ArrowsIsSink G q u ∧ ¬ ArrowsIsSource G q u ∧
    ¬ ArrowsIsSink G q v ∧ ¬ ArrowsIsSource G q v
