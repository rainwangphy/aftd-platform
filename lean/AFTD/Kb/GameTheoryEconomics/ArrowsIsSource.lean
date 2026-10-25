import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# ArrowsIsSource

Topic: combinatorial_games   Node: c9b7b1bdd65c

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

In a simple graph G and position p : ArrowsPos V, vertex u is a source if G.degree u ≥ 1 and for every neighbor v adjacent to u in G, p.1 u v is true.
-/

/-- Vertex u is a source in position p if degree u >= 1 and every neighbor v has an arrow out of u. -/
def ArrowsIsSource {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ArrowsPos V) (u : V) : Prop := G.degree u ≥ 1 ∧ ∀ v, G.Adj u v → p.1 u v
