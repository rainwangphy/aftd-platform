import AFTD.Prelude

/-!
# is_csym_matrix

Topic: graphs   Node: c851ef91c8e3

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 1

A real matrix A indexed by V is combinatorially symmetric and associated with the simple graph G if for all i, j in V, A i j is nonzero if and only if A j i is nonzero, and for all distinct i, j in V, A i j is nonzero if and only if i and j are adjacent in G.
-/

/-- A real matrix A is combinatorially symmetric with graph G if A_ij ≠ 0 ↔ A_ji ≠ 0 and for i ≠ j, A_ij ≠ 0 ↔ G.Adj i j. -/
def is_csym_matrix {V : Type*} (G : SimpleGraph V) (A : Matrix V V ℝ) : Prop := (∀ i j : V, A i j ≠ 0 ↔ A j i ≠ 0) ∧ (∀ i j : V, i ≠ j → (A i j ≠ 0 ↔ G.Adj i j))
