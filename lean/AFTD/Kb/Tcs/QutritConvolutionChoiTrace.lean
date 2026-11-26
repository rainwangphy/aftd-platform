import AFTD.Prelude
import AFTD.Kb.Tcs.QutritConvolutionChoi

/-!
# qutrit_convolution_choi_trace

Topic: quantum   Node: 3c3bac72b6a9

Provenance: helper lemma. Sanity lemma for the definition qutrit_convolution_choi, serving OP-2299.

For every complex 3×3 matrix σ, the trace of qutrit_convolution_choi σ equals the trace of σ; in particular the Choi matrix of a density matrix has trace 1.
-/

theorem qutrit_convolution_choi_trace (σ : Matrix (Fin 3) (Fin 3) ℂ) :
    (qutrit_convolution_choi σ).trace = σ.trace := by
  simp only [Matrix.trace, Matrix.diag, qutrit_convolution_choi, Matrix.of_apply,
    Fintype.sum_prod_type, Fin.sum_univ_three]
  simp
  have h1 : (-1 : Fin 3) = 2 := rfl
  have h2 : (-2 : Fin 3) = 1 := rfl
  rw [h1, h2]
  ring
