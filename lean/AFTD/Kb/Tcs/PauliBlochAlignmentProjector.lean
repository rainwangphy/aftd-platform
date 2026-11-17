import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBlochMatrix
import AFTD.Kb.Tcs.PauliBlochMatrixSquare
import AFTD.Kb.Tcs.PauliBlochAlignmentNumerator
import AFTD.Kb.Tcs.PauliBlochMatrixHermitian

/-!
# pauli_bloch_alignment_projector

Topic: quantum   Node: f84c458ff11b

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, Pauli alignment construction.

The unnormalized Pauli alignment conjugates the first Bloch projector to a positive scalar multiple of the second.
-/

theorem pauli_bloch_alignment_projector (b t : Fin 3 → ℝ)
    (hb : (∑ i, b i ^ 2) = 1) (ht : (∑ i, t i ^ 2) = 1) :
    let B := pauli_bloch_matrix b
    let T := pauli_bloch_matrix t
    let N := 1 + T * B
    N * (1 + B) * N.conjTranspose =
      ((2 * (1 + ∑ i, b i * t i) : ℝ) : ℂ) • (1 + T) := by
  dsimp
  let B := pauli_bloch_matrix b
  let T := pauli_bloch_matrix t
  let N := 1 + T * B
  let d : ℂ := ((2 * (1 + ∑ i, b i * t i) : ℝ) : ℂ)
  change N * (1 + B) * N.conjTranspose = d • (1 + T)
  have hB : B * B = 1 := by dsimp [B]; rw [pauli_bloch_matrix_square, hb]; simp
  have hT : T * T = 1 := by dsimp [T]; rw [pauli_bloch_matrix_square, ht]; simp
  have hNstar : N.conjTranspose = 1 + B * T := by
    dsimp [N, B, T]
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, pauli_bloch_matrix_hermitian]
  have hn : N.conjTranspose * N = d • 1 := by
    simpa [N, B, T, d] using (pauli_bloch_alignment_numerator b t hb ht).1
  have hint : T * N = N * B := by
    simpa [N, B, T] using (pauli_bloch_alignment_numerator b t hb ht).2
  have hcomm : N * N.conjTranspose = N.conjTranspose * N := by
    simp only [hNstar]
    dsimp [N]
    calc
      (1 + T * B) * (1 + B * T) = 1 + T * B + B * T + T * (B * B) * T := by noncomm_ring
      _ = 1 + T * B + B * T + 1 := by rw [hB]; simp [hT]
      _ = 1 + B * T + T * B + 1 := by abel
      _ = 1 + B * T + T * B + B * (T * T) * B := by rw [hT]; simp [hB]
      _ = (1 + B * T) * (1 + T * B) := by noncomm_ring
  have hn' : N * N.conjTranspose = d • 1 := hcomm.trans hn
  calc
    N * (1 + B) * N.conjTranspose =
        N * N.conjTranspose + (N * B) * N.conjTranspose := by noncomm_ring
    _ = N * N.conjTranspose + T * (N * N.conjTranspose) := by rw [← hint, Matrix.mul_assoc]
    _ = d • (1 + T) := by rw [hn']; simp [smul_add, Matrix.mul_smul]
