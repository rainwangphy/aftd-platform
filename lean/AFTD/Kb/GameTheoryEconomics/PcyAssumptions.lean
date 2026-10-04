import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpIsValid
import AFTD.Kb.GameTheoryEconomics.PcpMonotoneCostRatio
import AFTD.Kb.GameTheoryEconomics.PcpNoncompetitiveVenue
import AFTD.Kb.GameTheoryEconomics.PcyTheta
import AFTD.Kb.GameTheoryEconomics.PcyMu
import AFTD.Kb.GameTheoryEconomics.PcyCost

/-!
# pcy_assumptions

Topic: equilibria   Node: e29b6464797f

The three-type instance has strictly increasing types and satisfies the standing assumptions with alpha = 1/2, beta = 2, Assumption 1 and Assumption 2.
-/

/-- The three-type instance has strictly increasing types and satisfies the standing assumptions with `α = 1/2`, `β = 2`, Assumption 1 (MCR) and Assumption 2 (non-competitive venue 0). -/
lemma pcy_assumptions :
    StrictMono pcy_theta ∧ pcp_is_valid (1 / 2) 2 pcy_theta pcy_mu pcy_cost ∧
      pcp_monotone_cost_ratio pcy_theta pcy_cost ∧ pcp_noncompetitive_venue pcy_cost := by
  refine ⟨?_, ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all [pcy_theta] <;> norm_num
  · intro i; fin_cases i <;> simp [pcy_mu]
  · intro i; fin_cases i <;> simp [pcy_theta]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [pcy_cost]
  · intro i j j' h; fin_cases i <;> fin_cases j <;> fin_cases j' <;> simp_all [pcy_cost]
  · intro i i' j j' hθ h
    fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;> simp_all [pcy_theta, pcy_cost] <;> norm_num at *
  · intro i i' j hj
    have : j = 0 := Fin.ext hj
    subst this; fin_cases i <;> fin_cases i' <;> simp [pcy_cost]
