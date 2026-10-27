import AFTD.Prelude
import AFTD.Kb.Tcs.IsWeightedPartialPermutation
import AFTD.Kb.Tcs.CyclicMatrixFourier

/-!
# cyclic_fourier_col_zero_eq_zero_of_sharp

Topic: combinatorics   Node: 0d25fb364b2c

Provenance: helper lemma. step towards sharp_cyclic_graph_is_regular

For any weighted partial permutation matrix whose (0,0) entry is non-zero, every other entry (m,0) in the 0-th column is zero.
-/

/-- If the 2D Fourier transform is a weighted partial permutation matrix and entry (0,0) is nonzero, then all other entries (m,0) with m ≠ 0 in the 0-th column must vanish. -/
theorem cyclic_fourier_col_zero_eq_zero_of_sharp (N : ℕ) [NeZero N]
    (M : Matrix (ZMod N) (ZMod N) ℂ) (hs : is_weighted_partial_permutation (cyclic_matrix_fourier N M))
    (h0 : cyclic_matrix_fourier N M 0 0 ≠ 0) (m : ZMod N) (hm : m ≠ 0) :
    cyclic_matrix_fourier N M m 0 = 0 := by
  by_contra h
  exact hm (hs.2 0 0 m h0 h).symm
