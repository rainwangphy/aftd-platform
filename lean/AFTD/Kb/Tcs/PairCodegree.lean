import AFTD.Prelude

/-!
# pair_codegree

Topic: combinatorics   Node: 8068bbb442b2

Provenance: formalization of a published result. Source: arXiv:2611.12582 Section 1

The codegree of two vertices u and v in a hypergraph H is the number of hyperedges of H containing both u and v.
-/

/-- The codegree of a pair of vertices u, v in a 3-uniform hypergraph H is the number of edges containing both u and v. -/
def pair_codegree {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (u v : V) : ℕ := (H.filter (fun e => u ∈ e ∧ v ∈ e)).card
