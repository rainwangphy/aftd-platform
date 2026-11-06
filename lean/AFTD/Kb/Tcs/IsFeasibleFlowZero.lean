import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasibleFlow
import AFTD.Kb.Tcs.NonclairvoyantSchedulingOfflineOptZero

/-!
# is_feasible_flow_zero

Topic: online_algorithms   Node: 07323f7aa632

Provenance: helper lemma. arXiv:2611.05669, Section 4.1

For any natural number k, the zero flow (fun _ _ => 0) on Fin k is a feasible flow for the zero demand vector 0 : Fin k → ℝ.
-/

/-- The zero flow is feasible for the zero demand vector. -/
theorem is_feasible_flow_zero (k : ℕ) : is_feasible_flow (fun (_ _ : Fin k) => (0 : ℝ)) (0 : Fin k → ℝ) := by first | exact nonclairvoyant_scheduling_offline_opt_zero | (apply nonclairvoyant_scheduling_offline_opt_zero <;> assumption) | (apply nonclairvoyant_scheduling_offline_opt_zero <;> simp_all) | simpa using nonclairvoyant_scheduling_offline_opt_zero | (simp only [is_feasible_flow] at *; first | exact nonclairvoyant_scheduling_offline_opt_zero | (apply nonclairvoyant_scheduling_offline_opt_zero <;> assumption) | (apply nonclairvoyant_scheduling_offline_opt_zero <;> simp_all) | simpa using nonclairvoyant_scheduling_offline_opt_zero)
