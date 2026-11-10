import AFTD.Prelude

/-!
# graph_admits_involutory_weighted_adj_matrix

Topic: graphs   Node: 544b0cbbafdc

Provenance: formalization of a published result. Source: arXiv:2611.11813 Section 1

A simple graph G on a finite vertex type V admits an involutory weighted adjacency matrix over a field F if there exists a matrix A over F such that for all vertices u and v, A u v is non-zero if and only if u and v are adjacent in G, and A * A = 1.
-/

/-- A graph admits an involutory weighted adjacency matrix over F if there is a matrix A with A u v ≠ 0 ↔ G.Adj u v and A^2 = 1. -/
def graph_admits_involutory_weighted_adj_matrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Type*) [Field F] : Prop := ∃ A : Matrix V V F, (∀ u v, A u v ≠ 0 ↔ G.Adj u v) ∧ A * A = 1
