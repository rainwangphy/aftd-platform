import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph

/-!
# SignedGraph.edgeSign

Topic: combinatorics   Node: 68333f593a22

Provenance: formalization of a published result. Source: arXiv:2611.13901, Sec. 2.1

The extended edge sign between two vertices u and v in a signed graph G is the signature of the edge if u and v are adjacent, and 0 otherwise.
-/

/-- Extended edge sign between two vertices, taking value 0 for non-adjacent pairs. -/
noncomputable def SignedGraph.edgeSign {V : Type*} (G : SignedGraph V) (u v : V) : Int :=
  open Classical in if h : G.graph.Adj u v then G.sgn ⟨s(u, v), h⟩ else 0
