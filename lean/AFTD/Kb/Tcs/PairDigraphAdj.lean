import AFTD.Prelude

/-!
# pair_digraph_adj

Topic: combinatorics   Node: 31ef26c4167c

Provenance: formalization of a published result. Source: arXiv:2611.16654 Section 2

Two pairs P and Q of vertices form a directed arc P → Q in the pair digraph D(G) of a 3-uniform hypergraph G if both have cardinality 2 and every vertex of Q belongs to the neighborhood of P, so P ∪ {v} is an edge of G for each v in Q.
-/

/-- Directed adjacency in the pair digraph D(G) of a 3-uniform hypergraph: pair Q is contained in the common neighborhood of pair P. -/
def pair_digraph_adj {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (P Q : Finset α) : Prop := P.card = 2 ∧ Q.card = 2 ∧ ∀ v ∈ Q, P ∪ {v} ∈ G
