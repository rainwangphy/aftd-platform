import AFTD.Prelude

/-!
# complete_split_graph

Topic: graphs   Node: 7a1226c66a32

Provenance: formalization of a published result. Source: arXiv:2609.14826: Section 3

The complete split graph K_k + \bar{K}_{n-k} on vertex set Fin n, where vertices with index less than k form a clique and all edges exist between this clique and the remaining n-k independent vertices.
-/

/-- Complete split graph K_k + \bar{K}_{n-k} on Fin n. -/
def complete_split_graph (n k : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u.val < k ∨ v.val < k)
