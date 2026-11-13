import AFTD.Prelude
import AFTD.Kb.Tcs.DirectedMultigraph
import AFTD.Kb.Tcs.IsDirectedWalk
import AFTD.Kb.Tcs.WalkLengthENN

/-!
# directedDistENN

Topic: graphs   Node: dcc089d0f096

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 2

The shortest path distance directedDistENN G ℓ u v from vertex u to vertex v in a directed multigraph G with edge lengths ℓ : E → ENNReal, defined as the infimum of walkLengthENN ℓ p over all directed walks p from u to v.
-/

/-- Shortest path distance between two vertices in ENNReal, or top if unreachable. -/
noncomputable def directedDistENN {V E : Type*} (G : DirectedMultigraph V E) (ℓ : E → ENNReal) (u v : V) : ENNReal :=
  sInf { walkLengthENN ℓ p | (p : List E) (_ : IsDirectedWalk G u v p) }
