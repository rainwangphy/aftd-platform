import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaAdjMat
import AFTD.Kb.GameTheoryEconomics.GpaUStar
import AFTD.Kb.GameTheoryEconomics.GpaCube
import AFTD.Kb.GameTheoryEconomics.GpaAdjMatZeroOne
import AFTD.Kb.GameTheoryEconomics.GpaRhsAttain
import AFTD.Kb.GameTheoryEconomics.GpaPath3
import AFTD.Kb.GameTheoryEconomics.GpaPath3Indep

/-!
# gpa_cube_max_le_one_false

Topic: mechanism_design   Node: b07e79b077db

The auxiliary claim max_{x ∈ [0,1]^k} u*(x) ≤ 1 used in the proof of Eq. (5.4) of arXiv:2209.01146 is false: on the path with three vertices the maximum is 2.
-/

open Finset in
/-- The auxiliary claim `max_{x ∈ [0,1]^k} u*(x) ≤ 1` used in the proof of Eq. (5.4) of arXiv:2209.01146 is false: on the path with three vertices the maximum is `2`. -/
theorem gpa_cube_max_le_one_false :
    ¬ (∀ (k : ℕ) (e : Fin k → Fin k → ℝ), (∀ i j, e i j = 0 ∨ e i j = 1) →
        ∀ x : Fin k → ℝ, x ∈ gpa_cube k → gpa_uStar e x ≤ 1) := by
  intro h
  obtain ⟨hI, _⟩ := gpa_path3_indep
  obtain ⟨hmem, hval⟩ := gpa_rhs_attain gpa_path3 {0, 1} hI
  have := h 3 (gpa_adjMat gpa_path3) (gpa_adjMat_zero_one gpa_path3) _ hmem
  rw [hval] at this
  have hc : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  rw [hc] at this
  norm_num at this
