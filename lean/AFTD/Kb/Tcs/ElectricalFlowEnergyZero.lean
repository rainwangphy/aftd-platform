import AFTD.Prelude
import AFTD.Kb.Tcs.ElectricalFlowEnergy
import AFTD.Kb.Tcs.NonclairvoyantSchedulingOfflineOptZero

/-!
# electrical_flow_energy_zero

Topic: online_algorithms   Node: 71454f263adc

Provenance: helper lemma. arXiv:2611.05669, Section 4.1

For any natural number k and any resistance matrix d on Fin k, the electrical energy of the zero flow (fun _ _ => 0) is 0.
-/

/-- The electrical energy of the zero flow is zero. -/
theorem electrical_flow_energy_zero {k : ℕ} (d : Fin k → Fin k → ℝ) : electrical_flow_energy d (fun (_ _ : Fin k) => (0 : ℝ)) = 0 := by first | exact nonclairvoyant_scheduling_offline_opt_zero | (apply nonclairvoyant_scheduling_offline_opt_zero <;> assumption) | (apply nonclairvoyant_scheduling_offline_opt_zero <;> simp_all) | simpa using nonclairvoyant_scheduling_offline_opt_zero | (simp only [electrical_flow_energy] at *; first | exact nonclairvoyant_scheduling_offline_opt_zero | (apply nonclairvoyant_scheduling_offline_opt_zero <;> assumption) | (apply nonclairvoyant_scheduling_offline_opt_zero <;> simp_all) | simpa using nonclairvoyant_scheduling_offline_opt_zero)
