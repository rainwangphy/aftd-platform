import AFTD.Prelude
import AFTD.Kb.Tcs.ElectricalFlowEnergy

/-!
# electrical_flow_energy_expansion

Topic: online_algorithms   Node: 28bcd5cf8e8a

Provenance: helper lemma. arXiv:2611.05669, Appendix A

For any flows F, G : Fin k → Fin k → ℝ and resistance matrix d, the electrical energy of F + G equals the energy of F plus 2 * (∑ i, ∑ j with i < j, d i j * F i j * G i j) plus the energy of G.
-/

/-- Quadratic expansion of electrical flow energy for the sum of two flows. -/
theorem electrical_flow_energy_expansion {k : ℕ} (d : Fin k → Fin k → ℝ) (F G : Fin k → Fin k → ℝ) : electrical_flow_energy d (fun i j => F i j + G i j) = electrical_flow_energy d F + 2 * (∑ i : Fin k, ∑ j with i < j, d i j * F i j * G i j) + electrical_flow_energy d G := by
  unfold electrical_flow_energy
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  ext i
  congr 1
  ext j
  ring
