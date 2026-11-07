import AFTD.Prelude

/-!
# petrial_matrix

Topic: combinatorics   Node: 6d292aec8d5d

Provenance: formalization of a published result. Source: arXiv:2611.07503, Eq. (1)

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, and a finite subset F : Finset V, petrial_matrix G F is the V × V matrix over ZMod 2 defined as the sum of the adjacency matrix of G (over ZMod 2) and the diagonal matrix whose (v, v) diagonal entry is 1 if v ∈ F and 0 otherwise.
-/

/-- Diagonal perturbation of the adjacency matrix over GF(2) by a vertex subset. -/
noncomputable def petrial_matrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset V) : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2) + Matrix.diagonal (fun v => if v ∈ F then 1 else 0)
