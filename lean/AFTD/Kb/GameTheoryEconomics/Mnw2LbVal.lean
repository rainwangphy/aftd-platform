import AFTD.Prelude

/-!
# mnw2_lb_val

Topic: fair_division   Node: cd4664d3f854

Valuations of two agents over three goods, depending on a parameter ε: agent 0 has values (2/3, 1/3, 0) and agent 1 has values (4/7 − ε, 1/7 + ε, 2/7). For 0 < ε < 1/7 both are nonnegative and sum to 1.
-/

/-- The three-good, two-agent instance behind the 27/23 lower bound: agent 0 values (2/3, 1/3, 0), agent 1 values (4/7 − ε, 1/7 + ε, 2/7). -/
noncomputable def mnw2_lb_val (ε : ℝ) : Fin 2 → Fin 3 → ℝ :=
  ![![2 / 3, 1 / 3, 0], ![4 / 7 - ε, 1 / 7 + ε, 2 / 7]]
