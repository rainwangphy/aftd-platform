import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PellUnitSquared

/-!
# pell_log_shift_periodic

Topic: combinatorial_games   Node: cecb42b7e39c

Provenance: helper lemma. arXiv:2611.05898

For any function F : ℝ → ℝ satisfying Function.Periodic F 1 and any positive real number Y, evaluating F at Real.log (pell_unit_squared * Y) / Real.log pell_unit_squared equals F (Real.log Y / Real.log pell_unit_squared).
-/

/-- A 1-periodic function of the log-phase is invariant under multiplication of Y by the Pell unit P. -/
theorem pell_log_shift_periodic (F : ℝ → ℝ) (hF : Function.Periodic F 1) (Y : ℝ) (hY : 0 < Y) :
    F (Real.log (pell_unit_squared * Y) / Real.log pell_unit_squared) =
      F (Real.log Y / Real.log pell_unit_squared) := by
  have hP : 0 < pell_unit_squared := by unfold pell_unit_squared; positivity
  have hP1 : 1 < pell_unit_squared := by
    unfold pell_unit_squared
    have := Real.sqrt_nonneg 2
    linarith
  have hlog : Real.log pell_unit_squared ≠ 0 := ne_of_gt (Real.log_pos hP1)
  have hYne : Y ≠ 0 := ne_of_gt hY
  have hPne : pell_unit_squared ≠ 0 := ne_of_gt hP
  rw [Real.log_mul hPne hYne]
  have hsplit : (Real.log pell_unit_squared + Real.log Y) / Real.log pell_unit_squared
      = Real.log Y / Real.log pell_unit_squared + 1 := by
    field_simp
    ring
  rw [hsplit]
  exact hF _
