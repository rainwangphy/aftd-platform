import AFTD.Prelude

/-!
# cyclic_matrix_fourier

Topic: combinatorics   Node: 453992bfe18a

Provenance: formalization of a published result. Source: arXiv:2610.31807 Section 3, Equation (3.1)

The two-dimensional unitary Fourier transform of a matrix M indexed by ZMod N has (m,n)-entry equal to (1/N) ∑_{x,y} M(x,y) exp(-2πi(mx+ny)/N).
-/

/-- Two-dimensional unitary Fourier transform of a matrix on ZMod N x ZMod N. -/
noncomputable def cyclic_matrix_fourier (N : ℕ) [NeZero N] (M : Matrix (ZMod N) (ZMod N) ℂ) :
    Matrix (ZMod N) (ZMod N) ℂ := Matrix.of fun m n => (1 / (N : ℂ)) * ∑ x : ZMod N, ∑ y : ZMod N,
    M x y * Complex.exp (-2 * Real.pi * Complex.I * ((m * x + n * y).val / (N : ℂ)))
