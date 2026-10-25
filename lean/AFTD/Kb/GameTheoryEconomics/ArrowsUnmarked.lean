import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# ArrowsUnmarked

Topic: combinatorial_games   Node: b5138cad7651

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

In a simple graph G and position p : ArrowsPos V, vertices u and v form an unmarked edge if G.Adj u v and both p.1 u v and p.1 v u are false.
-/

/-- An edge {u, v} in G is unmarked in position p if neither directed edge is true. -/
def ArrowsUnmarked {V : Type*} (G : SimpleGraph V) (p : ArrowsPos V) (u v : V) : Prop := G.Adj u v ∧ ¬ p.1 u v ∧ ¬ p.1 v u
