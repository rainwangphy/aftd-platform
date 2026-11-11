import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphEdgeSign

/-!
# SignedGraph.netDegree

Topic: combinatorics   Node: 38b703316df1

Provenance: formalization of a published result. Source: arXiv:2611.13901, Sec. 2.1

The net-degree of a vertex v in a finite signed graph G is the sum over all vertices w of the extended edge sign between v and w.
-/

/-- Net-degree of a vertex is the sum of edge signs incident to it. -/
noncomputable def SignedGraph.netDegree {V : Type*} [Fintype V] (G : SignedGraph V) (v : V) : Int :=
  open scoped BigOperators in open Classical in ∑ w : V, G.edgeSign v w
