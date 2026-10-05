import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseCost
import AFTD.Kb.GameTheoryEconomics.FseSinglePeaked
import AFTD.Kb.GameTheoryEconomics.FseQ0

/-!
# fse_q0_not_singlePeaked

Topic: mechanism_design   Node: a03888345dde

Under q0, the preference of the agent located at 0 is not single-peaked: the facility at 1/2 costs her 11/40, but the farther location 1 costs only 1/10.
-/

/-- Under `q0`, the preference of the agent located at `0` is not single-peaked: the facility at `1/2` costs her `11/40`, but the farther location `1` costs only `1/10`. -/
theorem fse_q0_not_singlePeaked : ¬ fse_SinglePeaked fse_q0 0 := by
  intro h
  have := h (1 / 2) 1 (by norm_num) (by norm_num) (Or.inl ⟨by norm_num, by norm_num⟩)
  simp only [fse_cost, fse_q0] at this
  norm_num [abs_of_neg] at this
