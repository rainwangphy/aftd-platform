import AFTD.Prelude
import AFTD.Kb.Tcs.IsWeightedPartialPermutation
import AFTD.Kb.Tcs.CyclicMatrixFourier

/-!
# is_sharp_cyclic_labeling

Topic: combinatorics   Node: 83bad27c54db

Provenance: formalization of a published result. Source: arXiv:2610.31807 Definition 3.12 and Theorem 3.13

A bijection π from ZMod N to the vertex set of a simple graph G is a sharp cyclic labeling if the two-dimensional Fourier transform of the adjacency matrix under π is a weighted partial permutation matrix.
-/

/-- A cyclic labeling π : ZMod N ≃ V is sharp for a simple graph G if the Fourier transform of its adjacency matrix is a weighted partial permutation matrix. -/
noncomputable def is_sharp_cyclic_labeling {V : Type*} (N : ℕ) [NeZero N]
    (G : SimpleGraph V) [DecidableRel G.Adj] (π : ZMod N ≃ V) : Prop := is_weighted_partial_permutation (cyclic_matrix_fourier N (Matrix.of fun x y => if G.Adj (π x) (π y) then 1 else 0))
