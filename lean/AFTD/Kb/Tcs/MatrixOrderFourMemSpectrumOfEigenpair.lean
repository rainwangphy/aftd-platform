import AFTD.Prelude

/-!
# matrix_order_four_mem_spectrum_of_eigenpair

Topic: graphs   Node: 12444f2b7865

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

A nonzero complex eigenvector witnesses membership in the spectrum of an order-four real matrix.
-/

theorem matrix_order_four_mem_spectrum_of_eigenpair
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℂ) (hv0 : v ≠ 0) (z : ℂ)
    (hv : (L.map (algebraMap ℝ ℂ)).mulVec v = z • v) :
    z ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)) := by
  rw [← Matrix.spectrum_toLin']
  apply Module.End.HasEigenvalue.mem_spectrum
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  exact ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
