import AFTD.Prelude

/-!
# is_l_matrix

Topic: combinatorics   Node: 050ef9e9d2c6

Provenance: formalization of a published result. Source: arXiv:2610.39908, Section 1, Low-rank matrices with three prescribed off-diagonal values over F_p

A square matrix $M \in \mathrm{Mat}_n(K)$ is an $L$-matrix if its diagonal entries are zero and its off-diagonal entries belong to $L$.
-/

/-- A square matrix is an L-matrix if all its diagonal entries are 0 and all its off-diagonal entries belong to L. -/
def is_l_matrix {n : ℕ} {K : Type*} [Zero K] (M : Matrix (Fin n) (Fin n) K) (L : Set K) : Prop := (∀ i, M i i = 0) ∧ (∀ i j, i ≠ j → M i j ∈ L)
