import AFTD.Prelude

/-!
# ef1_cost_gap_instance

Topic: fair_division   Node: 1937bdd5bbbf

The two-agent instance with costs (0, 1/2, 1/2) and (1/3 - 2d, 1/3 + d, 1/3 + d).
-/

/-- The two-agent instance with three chores attaining a gap of `1/6 - δ`: agent 0 has costs `(0, 1/2, 1/2)`, agent 1 has costs `(1/3 - 2δ, 1/3 + δ, 1/3 + δ)`. -/
noncomputable def ef1_cost_gap_instance (δ : ℝ) : Fin 2 → Fin 3 → ℝ :=
  ![![0, 1/2, 1/2], ![1/3 - 2 * δ, 1/3 + δ, 1/3 + δ]]
