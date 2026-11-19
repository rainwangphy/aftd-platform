import AFTD.Prelude
import AFTD.Kb.Physics.Op2046Prob
import AFTD.Kb.Physics.Op2046Spectrum
import AFTD.Kb.Physics.Op2046Majorizes

/-!
# op2046_wishart_probability_bounds

Topic: quantum_mechanics   Node: c8fd0ec0f37c

Provenance: helper lemma. Probability-measure sanity check for OP-2046.

The probability of normalized-spectrum majorization for the two independent Gaussian Gram matrices lies between zero and one, for all dimensions.
-/

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section

theorem op2046_wishart_probability_bounds (n m h : ℕ) :
  0 ≤ op2046_prob n m h ∧ op2046_prob n m h ≤ 1 := by
  have hbound :
      (Measure.pi (fun _ : Fin n × Fin m × Fin 2 => gaussianReal (0:ℝ) (1/2 : NNReal))).prod
        (Measure.pi (fun _ : Fin n × Fin (m+h) × Fin 2 => gaussianReal (0:ℝ) (1/2 : NNReal)))
        {z | op2046_majorizes n (op2046_spectrum n m z.1)
          (op2046_spectrum n (m+h) z.2)} ≤ 1 := by
    rw [← measure_univ (μ := (Measure.pi (fun _ : Fin n × Fin m × Fin 2 =>
        gaussianReal (0:ℝ) (1/2 : NNReal))).prod
      (Measure.pi (fun _ : Fin n × Fin (m+h) × Fin 2 => gaussianReal (0:ℝ) (1/2 : NNReal))))]
    exact measure_mono (Set.subset_univ _)
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold op2046_prob
  dsimp only
  exact ENNReal.toReal_mono (by simp) hbound
