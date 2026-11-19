import AFTD.Prelude

/-!
# is_k_extendable

Topic: graphs   Node: 57d2768195ce

Provenance: formalization of a published result. Source: arXiv:2611.22690, Section 2 (definition of k-extendable graphs); matchings are Mathlib subgraphs with IsMatching, size = ncard of the edge set

For a finite vertex type V (with [Fintype V]), a simple graph G : SimpleGraph V and k : ℕ, is_k_extendable G k is the Prop that is the conjunction of three conditions: (1) 2 * k + 2 ≤ Fintype.card V; (2) there is a subgraph M : G.Subgraph with M.IsMatching and M.edgeSet.ncard = k (a matching with exactly k edges); (3) for every subgraph M : G.Subgraph with M.IsMatching and M.edgeSet.ncard = k there is a subgraph P : G.Subgraph with P.IsPerfectMatching and M ≤ P (every k-matching extends to a perfect matching).
-/

/-- G is k-extendable: at least 2k+2 vertices, has a k-matching, and every k-matching extends to a perfect matching. -/
def is_k_extendable {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  2 * k + 2 ≤ Fintype.card V ∧
  (∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k) ∧
  ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard = k →
    ∃ P : G.Subgraph, P.IsPerfectMatching ∧ M ≤ P
