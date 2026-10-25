import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# ArrowsIsSink

Topic: combinatorial_games   Node: 312cac5e748f

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

In a simple graph G and position p : ArrowsPos V, vertex u is a sink if G.degree u ≥ 1 and for every neighbor v adjacent to u in G, p.1 v u is true.
-/

/-- Vertex u is a sink in position p if degree u >= 1 and every neighbor v has an arrow into u. -/
def ArrowsIsSink {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ArrowsPos V) (u : V) : Prop := G.degree u ≥ 1 ∧ ∀ v, G.Adj u v → p.1 v u
