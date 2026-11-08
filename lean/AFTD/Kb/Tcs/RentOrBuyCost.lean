import AFTD.Prelude
import AFTD.Kb.Tcs.ScheduleHistory

/-!
# rent_or_buy_cost

Topic: online_algorithms   Node: bbe2dbe0e6ab

Provenance: formalization of a published result. Source: arXiv:2611.06955, Definition 3

Given horizon T : ℕ, increments a : Fin (T - 1) → NNReal, reset price K : ℝ, and a schedule r : Fin T → Bool, rent_or_buy_cost T a K r : ℝ is the sum over all calls t : Fin T of (schedule_history T a r t : ℝ) + (if r t then K else 0).
-/

/-- The total cost of a schedule r on a session of horizon T with increments a and reset price K. -/
noncomputable def rent_or_buy_cost (T : ℕ) (a : Fin (T - 1) → NNReal) (K : ℝ) (r : Fin T → Bool) : ℝ := ∑ t : Fin T, ((schedule_history T a r t : ℝ) + if r t then K else 0)
