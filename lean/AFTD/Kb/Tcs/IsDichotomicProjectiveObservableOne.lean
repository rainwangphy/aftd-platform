import AFTD.Prelude
import AFTD.Kb.Tcs.IsDichotomicProjectiveObservable
import AFTD.Kb.Tcs.ThreeQubitThreePairwiseZeroAxes

/-!
# is_dichotomic_projective_observable_one

Topic: quantum   Node: 3484b92ebc53

Provenance: helper lemma. arXiv:2610.35838 Sec. II.3

The d × d identity matrix over ℂ is a dichotomic projective observable on ℂ^d.
-/

/-- The identity matrix on C^d is a dichotomic projective observable. -/
theorem is_dichotomic_projective_observable_one (d : ℕ) :
    is_dichotomic_projective_observable (1 : Matrix (Fin d) (Fin d) ℂ) := by first | exact three_qubit_three_pairwise_zero_axes | (apply three_qubit_three_pairwise_zero_axes <;> assumption) | (apply three_qubit_three_pairwise_zero_axes <;> simp_all) | simpa using three_qubit_three_pairwise_zero_axes | (simp only [is_dichotomic_projective_observable] at *; first | exact three_qubit_three_pairwise_zero_axes | (apply three_qubit_three_pairwise_zero_axes <;> assumption) | (apply three_qubit_three_pairwise_zero_axes <;> simp_all) | simpa using three_qubit_three_pairwise_zero_axes)
