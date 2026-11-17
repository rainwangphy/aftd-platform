import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBlochMatrix
import AFTD.Kb.Tcs.PauliBlochAlignmentProjector

/-!
# pauli_spinor_alignment_pointwise

Topic: quantum   Node: 6a876c26a172

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, Pauli alignment construction.

For unit Bloch axes with positive alignment denominator, the normalized Pauli alignment transforms any spinor with the first axis projector into one with the second.
-/

theorem pauli_spinor_alignment_pointwise (b t : Fin 3 → ℝ) (u : Fin 2 → ℂ)
    (hb : (∑ i, b i ^ 2) = 1) (ht : (∑ i, t i ^ 2) = 1)
    (hpos : 0 < 1 + ∑ i, b i * t i)
    (hu : ∀ i j, u i * star (u j) = (1 + pauli_bloch_matrix b) i j / 2) :
    let N := 1 + pauli_bloch_matrix t * pauli_bloch_matrix b
    let d := Real.sqrt (2 * (1 + ∑ i, b i * t i))
    let v : Fin 2 → ℂ := fun i => (N.mulVec u) i / (d : ℂ)
    ∀ i j, v i * star (v j) = (1 + pauli_bloch_matrix t) i j / 2 := by
  dsimp
  let B := pauli_bloch_matrix b
  let T := pauli_bloch_matrix t
  let N := 1 + T * B
  let d : ℝ := 2 * (1 + ∑ i, b i * t i)
  let V : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of (fun i j => u i * star (u j))
  change ∀ i j, ((N.mulVec u) i / (Real.sqrt d : ℂ)) *
    star ((N.mulVec u) j / (Real.sqrt d : ℂ)) = (1 + T) i j / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hV : V = (2 : ℂ)⁻¹ • (1 + B) := by
    ext i j
    simpa [V, B, div_eq_mul_inv, mul_comm] using hu i j
  have houter : Matrix.of (fun i j => (N.mulVec u) i * star ((N.mulVec u) j)) =
      N * V * N.conjTranspose := by
    ext i j
    simp [V, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, map_add, map_mul]
    ring
  have hproj : N * (1 + B) * N.conjTranspose = (d : ℂ) • (1 + T) := by
    simpa [N, B, T, d] using pauli_bloch_alignment_projector b t hb ht
  have hall : N * V * N.conjTranspose = ((2 : ℂ)⁻¹ * (d : ℂ)) • (1 + T) := by
    rw [hV]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [hproj, smul_smul]
  have hsqrt_ne : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 hd)
  have hsqrt_sq : (Real.sqrt d : ℂ)^2 = (d : ℂ) := by
    exact_mod_cast (Real.sq_sqrt hd.le)
  intro i j
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j) (houter.trans hall)
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at hentry
  simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
  field_simp [hsqrt_ne]
  simp only [Complex.star_def] at hentry
  rw [← hsqrt_sq] at hentry
  linear_combination 2 * hentry
