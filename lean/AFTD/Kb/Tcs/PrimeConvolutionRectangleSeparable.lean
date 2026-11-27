import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsSeparable

/-!
# prime_convolution_rectangle_separable

Topic: quantum   Node: 163825a5f96d

Provenance: helper lemma. OP-2466 four-phase product rectangle certificate, experiment 42729

A two-corner rank-one operator plus the geometric-mean diagonal terms on the crossed corners is separable; four phase-averaged product projectors give an exact decomposition.
-/

private def in1249_phase4 : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]
def prime_convolution_rectangle_delta {n : ℕ} (i j : Fin n) : ℂ := if i = j then 1 else 0
@[simp] private theorem star_prime_convolution_rectangle_delta {n : ℕ} (i j : Fin n) : star (prime_convolution_rectangle_delta i j) = prime_convolution_rectangle_delta i j := by
  simp [prime_convolution_rectangle_delta]
set_option maxHeartbeats 1000000

theorem prime_convolution_rectangle_separable (d : ℕ) (a b c e : Fin d)
    (A B : ℝ) :
    matrix_is_separable d d (Matrix.of fun z w =>
      ((A : ℂ)^2 * prime_convolution_rectangle_delta z.1 a * prime_convolution_rectangle_delta z.2 c +
       (B : ℂ)^2 * prime_convolution_rectangle_delta z.1 b * prime_convolution_rectangle_delta z.2 e) *
      star ((A : ℂ)^2 * prime_convolution_rectangle_delta w.1 a * prime_convolution_rectangle_delta w.2 c +
       (B : ℂ)^2 * prime_convolution_rectangle_delta w.1 b * prime_convolution_rectangle_delta w.2 e) +
      ((A : ℂ)^2 * (B : ℂ)^2) *
        (prime_convolution_rectangle_delta z.1 a * prime_convolution_rectangle_delta z.2 e * prime_convolution_rectangle_delta w.1 a * prime_convolution_rectangle_delta w.2 e +
         prime_convolution_rectangle_delta z.1 b * prime_convolution_rectangle_delta z.2 c * prime_convolution_rectangle_delta w.1 b * prime_convolution_rectangle_delta w.2 c)) := by
  classical
  refine ⟨4,
    (fun k i => ((A : ℂ) * prime_convolution_rectangle_delta i a + in1249_phase4 k * (B : ℂ) * prime_convolution_rectangle_delta i b) / 2),
    (fun k i => ((A : ℂ) * prime_convolution_rectangle_delta i c + star (in1249_phase4 k) * (B : ℂ) * prime_convolution_rectangle_delta i e)), ?_⟩
  intro z w
  simp [Fin.sum_univ_succ, in1249_phase4, star_add, star_mul, star_div₀,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I, star_prime_convolution_rectangle_delta]
  ring_nf
  simp [Complex.I_sq]
  norm_num
  ring
