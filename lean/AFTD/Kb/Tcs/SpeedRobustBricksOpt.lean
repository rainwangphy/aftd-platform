import AFTD.Prelude
import AFTD.Kb.Tcs.SpeedRobustBricksTotalCompletionTime

/-!
# speed_robust_bricks_opt

Topic: online_algorithms   Node: eaaf1ea862b7

Provenance: formalization of a published result. Source: arXiv:2611.20795 Section 2

Defines the noncomputable function speed_robust_bricks_opt n m for natural numbers n and m as the infimum ⨅ σ : Fin n → Fin m, speed_robust_bricks_total_completion_time σ, representing the unrestricted offline optimal total completion time of n unit-size jobs on m identical unit-speed machines.
-/

/-- The unrestricted offline optimal total completion time of n unit-size jobs on m identical machines. -/
noncomputable def speed_robust_bricks_opt (n m : ℕ) : ℕ := ⨅ σ : Fin n → Fin m, speed_robust_bricks_total_completion_time σ
