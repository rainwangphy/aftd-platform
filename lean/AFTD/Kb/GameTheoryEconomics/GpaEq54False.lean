import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaLhsSet
import AFTD.Kb.GameTheoryEconomics.GpaRhsSet
import AFTD.Kb.GameTheoryEconomics.GpaAdjMatZeroOne
import AFTD.Kb.GameTheoryEconomics.GpaLhsIsGreatest
import AFTD.Kb.GameTheoryEconomics.GpaRhsIsGreatest
import AFTD.Kb.GameTheoryEconomics.GpaEq54FailsOfIndep
import AFTD.Kb.GameTheoryEconomics.GpaPath3
import AFTD.Kb.GameTheoryEconomics.GpaPath3Indep

/-!
# gpa_eq54_false

Topic: mechanism_design   Node: 73d3e4b28c0a

Eq. (5.4) in the proof of Theorem 5 (hardness of costly information acquisition) of arXiv:2209.01146 is false: it is not true that for every 0/1 matrix e the maximum of u*(σ) - h(σ) over the simplex equals (1/k) times the maximum of u* over the cube. On the path with three vertices the left side is 5/6 and the right side is 2/3.
-/

open Finset in
/-- Eq. (5.4) in the proof of Theorem 5 (hardness of costly information acquisition) of arXiv:2209.01146 is false: it is not true that for every 0/1 matrix `e` the maximum of `u*(σ) - h(σ)` over the simplex equals `(1/k)` times the maximum of `u*` over the cube. On the path with three vertices the left side is `5/6` and the right side is `2/3`. -/
theorem gpa_eq54_false :
    ¬ (∀ (k : ℕ) (e : Fin k → Fin k → ℝ), (∀ i j, e i j = 0 ∨ e i j = 1) → ∀ (L R : ℝ),
        IsGreatest (gpa_lhsSet e) L → IsGreatest (gpa_rhsSet e) R → L = R / (k : ℝ)) := by
  intro h
  obtain ⟨hI, hmax⟩ := gpa_path3_indep
  have hc : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have hL := gpa_lhs_isGreatest gpa_path3 {0, 1} hI hmax (by rw [hc]; norm_num)
    (by rw [hc]; norm_num)
  have hR := gpa_rhs_isGreatest gpa_path3 {0, 1} hI hmax
  have hlt := gpa_eq54_fails_of_indep gpa_path3 {0, 1} hI hmax (by rw [hc]) (by rw [hc]; norm_num)
    _ _ hL hR
  have := h 3 (gpa_adjMat gpa_path3) (gpa_adjMat_zero_one gpa_path3) _ _ hL hR
  linarith
