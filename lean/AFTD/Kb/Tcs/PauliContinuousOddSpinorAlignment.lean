import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBlochMatrix
import AFTD.Kb.Tcs.PauliSpinorAlignmentPointwise

/-!
# pauli_continuous_odd_spinor_alignment

Topic: quantum   Node: c7994551d50d

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, continuous odd Pauli alignment.

Continuous even unit Bloch-axis families and a continuous odd spinor family can be aligned continuously and oddly to the target axes when the alignment denominator is positive.
-/

theorem pauli_continuous_odd_spinor_alignment
    (b t : (Fin 4 → ℝ) → Fin 3 → ℝ)
    (u : (Fin 4 → ℝ) → Fin 2 → ℂ)
    (hbcont : ∀ i, ContinuousOn (fun q => b q i) {q | (∑ k, (q k)^2) = 1})
    (htcont : ∀ i, ContinuousOn (fun q => t q i) {q | (∑ k, (q k)^2) = 1})
    (hucont : ∀ i, ContinuousOn (fun q => u q i) {q | (∑ k, (q k)^2) = 1})
    (hbeven : ∀ q, (∑ k, (q k)^2) = 1 → b (-q) = b q)
    (hteven : ∀ q, (∑ k, (q k)^2) = 1 → t (-q) = t q)
    (huodd : ∀ q, (∑ k, (q k)^2) = 1 → u (-q) = -u q)
    (hb : ∀ q, (∑ k, (q k)^2) = 1 → (∑ i, b q i ^ 2) = 1)
    (ht : ∀ q, (∑ k, (q k)^2) = 1 → (∑ i, t q i ^ 2) = 1)
    (hpos : ∀ q, (∑ k, (q k)^2) = 1 → 0 < 1 + ∑ i, b q i * t q i)
    (hu : ∀ q, (∑ k, (q k)^2) = 1 → ∀ i j,
      u q i * star (u q j) = (1 + pauli_bloch_matrix (b q)) i j / 2) :
    ∃ v : (Fin 4 → ℝ) → Fin 2 → ℂ,
      (∀ i, ContinuousOn (fun q => v q i) {q | (∑ k, (q k)^2) = 1}) ∧
      (∀ q, (∑ k, (q k)^2) = 1 → v (-q) = -v q) ∧
      (∀ q, (∑ k, (q k)^2) = 1 → ∀ i j,
        v q i * star (v q j) = (1 + pauli_bloch_matrix (t q)) i j / 2) := by
  let S : Set (Fin 4 → ℝ) := {q | (∑ k, (q k)^2) = 1}
  let N := fun q => 1 + pauli_bloch_matrix (t q) * pauli_bloch_matrix (b q)
  let den := fun q => Real.sqrt (2 * (1 + ∑ i, b q i * t q i))
  let v : (Fin 4 → ℝ) → Fin 2 → ℂ := fun q i => (N q).mulVec (u q) i / (den q : ℂ)
  refine ⟨v, ?_, ?_, ?_⟩
  · have hbmat : ∀ i j, ContinuousOn (fun q => pauli_bloch_matrix (b q) i j) S := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [pauli_bloch_matrix] <;> fun_prop (disch := first | assumption | exact hbcont _)
    have htmat : ∀ i j, ContinuousOn (fun q => pauli_bloch_matrix (t q) i j) S := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [pauli_bloch_matrix] <;> fun_prop (disch := first | assumption | exact htcont _)
    have hN : ∀ i j, ContinuousOn (fun q => N q i j) S := by
      intro i j
      dsimp [N]
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
      fun_prop (disch := first | assumption | exact hbmat _ _ | exact htmat _ _)
    have hden : ContinuousOn den S := by
      dsimp [den]
      fun_prop (disch := first | assumption | exact hbcont _ | exact htcont _)
    intro i
    dsimp [v]
    apply ContinuousOn.div
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      fun_prop (disch := first | assumption | exact hN _ _ | exact hucont _)
    · exact Complex.continuous_ofReal.comp_continuousOn hden
    · intro q hq
      have hp : 0 < 2 * (1 + ∑ i, b q i * t q i) := by
        have := hpos q hq
        positivity
      exact_mod_cast (Real.sqrt_ne_zero'.2 hp)
  · intro q hq
    funext i
    dsimp [v, N, den]
    rw [hbeven q hq, hteven q hq, huodd q hq]
    simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
    rw [← neg_div]
    congr 1 <;> abel
  · intro q hq i j
    exact pauli_spinor_alignment_pointwise (b q) (t q) (u q)
      (hb q hq) (ht q hq) (hpos q hq) (hu q hq) i j
