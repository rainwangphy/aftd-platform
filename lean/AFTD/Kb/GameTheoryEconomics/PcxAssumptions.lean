import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpIsValid
import AFTD.Kb.GameTheoryEconomics.PcpMonotoneCostRatio
import AFTD.Kb.GameTheoryEconomics.PcpNoncompetitiveVenue
import AFTD.Kb.GameTheoryEconomics.PcxTheta
import AFTD.Kb.GameTheoryEconomics.PcxMu
import AFTD.Kb.GameTheoryEconomics.PcxCost

/-!
# pcx_assumptions

Topic: equilibria   Node: d7664e2e4c43

The binary instance satisfies the standing assumptions with alpha = 1/2, beta = 2, Assumption 1 (MCR) and Assumption 2 (non-competitive venue).
-/

/-- The instance satisfies the standing assumptions with `α = 1/2`, `β = 2`, together with Assumption 1 (MCR) and Assumption 2 (non-competitive venue 0). -/
lemma pcx_assumptions :
    pcp_is_valid (1 / 2) 2 pcx_theta pcx_mu pcx_cost ∧ pcp_monotone_cost_ratio pcx_theta pcx_cost ∧
      pcp_noncompetitive_venue pcx_cost := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [pcx_mu]
  · intro i; fin_cases i <;> simp [pcx_theta]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [pcx_cost]
  · intro i j j' h; fin_cases i <;> fin_cases j <;> fin_cases j' <;> simp_all [pcx_cost]
  · intro i i' j j' hθ h
    fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;> simp_all [pcx_theta, pcx_cost]; norm_num
  · intro i i' j hj
    have : j = 0 := Fin.ext hj
    subst this; fin_cases i <;> fin_cases i' <;> simp [pcx_cost]
