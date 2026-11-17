import AFTD.Prelude
import AFTD.Kb.Tcs.QuaternionSpinorMatrix
import AFTD.Kb.Tcs.QuaternionBlochRotation
import AFTD.Kb.Tcs.PauliBlochMatrix
import AFTD.Kb.Tcs.QuaternionSpinorPauliConjugation
import AFTD.Kb.Tcs.QuaternionSpinorUnitaryScaled

/-!
# quaternion_spinor_projector

Topic: quantum   Node: 90652a4b09af

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion reference spinor construction.

A unit quaternion rotates a spinor and its Bloch projector consistently.
-/

theorem quaternion_spinor_projector (q : Fin 4 → ℝ) (b : Fin 3 → ℝ)
    (u : Fin 2 → ℂ) (hq : (∑ i, (q i)^2) = 1)
    (hu : ∀ i j, u i * star (u j) = (1 + pauli_bloch_matrix b) i j / 2) :
    ∀ i j, ((quaternion_spinor_matrix q).mulVec u) i *
      star (((quaternion_spinor_matrix q).mulVec u) j) =
      (1 + pauli_bloch_matrix ((quaternion_bloch_rotation q).mulVec b)) i j / 2 := by
  let U := quaternion_spinor_matrix q
  let B := pauli_bloch_matrix b
  let C := pauli_bloch_matrix ((quaternion_bloch_rotation q).mulVec b)
  let V : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of (fun i j => u i * star (u j))
  have hV : V = (2 : ℂ)⁻¹ • (1 + B) := by
    ext i j
    simpa [V, B, div_eq_mul_inv, mul_comm] using hu i j
  have houter : Matrix.of (fun i j => (U.mulVec u) i * star ((U.mulVec u) j)) =
      U * V * U.conjTranspose := by
    ext i j
    simp [V, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, map_add, map_mul]
    ring
  have hU : U * U.conjTranspose = 1 := by
    simpa [U, hq] using quaternion_spinor_unitary_scaled q
  have hrot : U * B * U.conjTranspose = C := by
    simpa [U, B, C] using quaternion_spinor_pauli_conjugation q b
  have hfinal : U * V * U.conjTranspose = (2 : ℂ)⁻¹ • (1 + C) := by
    rw [hV]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc
      U * (1 + B) * U.conjTranspose = U * U.conjTranspose + U * B * U.conjTranspose := by
        simp [Matrix.mul_add, Matrix.add_mul]
      _ = 1 + C := by rw [hU, hrot]
  intro i j
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j) (houter.trans hfinal)
  simpa [U, C, div_eq_mul_inv, mul_comm] using hentry
