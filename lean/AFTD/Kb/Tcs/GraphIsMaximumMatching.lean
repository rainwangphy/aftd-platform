import AFTD.Prelude
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# graph_is_maximum_matching

Topic: approximation   Node: 2da9a4e09491

Provenance: formalization of a published result. Source: arXiv:2610.27833, Section 1.1

A subgraph M of a simple graph G is a maximum matching if M is a matching and its edge cardinality equals the matching number of G.
-/

/-- A subgraph M of G is a maximum matching if M is a matching and |M| = ν(G). -/
def graph_is_maximum_matching {V : Type*} (G : SimpleGraph V) (M : G.Subgraph) : Prop := M.IsMatching ∧ M.edgeSet.encard = graph_matching_num G
