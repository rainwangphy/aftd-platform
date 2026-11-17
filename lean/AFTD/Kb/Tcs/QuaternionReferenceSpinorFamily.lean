import AFTD.Prelude
import AFTD.Kb.Tcs.QuaternionSpinorMatrix
import AFTD.Kb.Tcs.QuaternionBlochRotation
import AFTD.Kb.Tcs.PauliBlochMatrix
import AFTD.Kb.Tcs.QuaternionSpinorProjector
import AFTD.Kb.Tcs.QuaternionSpinorOdd

/-!
# quaternion_reference_spinor_family

Topic: quantum   Node: 468b3ae1a111

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, quaternion reference spinor construction.

A fixed reference spinor acted on by a fixed quaternion and a varying quaternion gives a continuous odd spinor family with the displayed Bloch projector.
-/

theorem quaternion_reference_spinor_family (q0 : Fin 4 → ℝ) (b : Fin 3 → ℝ)
    (u0 : Fin 2 → ℂ) (hq0 : (∑ i, (q0 i)^2) = 1)
    (hu0 : ∀ i j, u0 i * star (u0 j) = (1 + pauli_bloch_matrix b) i j / 2) :
    ∃ u : (Fin 4 → ℝ) → Fin 2 → ℂ,
      (∀ i, ContinuousOn (fun q => u q i) {q | (∑ k, (q k)^2) = 1}) ∧
      (∀ q, (∑ k, (q k)^2) = 1 → u (-q) = -u q) ∧
      (∀ q, (∑ k, (q k)^2) = 1 → ∀ i j,
        u q i * star (u q j) =
          (1 + pauli_bloch_matrix ((quaternion_bloch_rotation q0).mulVec
            ((quaternion_bloch_rotation q).mulVec b))) i j / 2) := by
  let u : (Fin 4 → ℝ) → Fin 2 → ℂ := fun q =>
    (quaternion_spinor_matrix q0).mulVec ((quaternion_spinor_matrix q).mulVec u0)
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [u, quaternion_spinor_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      fun_prop
  · intro q hq
    funext i
    dsimp [u]
    rw [quaternion_spinor_odd]
    simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib] <;> ring
  · intro q hq
    have hfirst := quaternion_spinor_projector q b u0 hq hu0
    exact quaternion_spinor_projector q0 ((quaternion_bloch_rotation q).mulVec b)
      ((quaternion_spinor_matrix q).mulVec u0) hq0 hfirst
