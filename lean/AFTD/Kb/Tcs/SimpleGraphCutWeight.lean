import AFTD.Prelude

/-!
# simple_graph_cut_weight

Topic: graphs   Node: 1a321f719c57

Provenance: formalization of a published result. Source: arXiv:2611.05178 Section 1

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, an edge weighting w : G.edgeSet → ℝ, and a vertex subset S : Finset V, the cut weight simple_graph_cut_weight G w S is defined as the sum over all edges e : G.edgeSet of w e if there exist u ∈ S and v ∉ S such that (e : Sym2 V) = s(u, v), and 0 otherwise.
-/

/-- The total weight of edges crossing between S and its complement in an edge-weighted simple graph. -/
noncomputable def simple_graph_cut_weight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : G.edgeSet → ℝ) (S : Finset V) : ℝ := ∑ e : G.edgeSet, if ∃ u ∈ S, ∃ v ∉ S, (e : Sym2 V) = s(u, v) then w e else 0
