import AFTD.Prelude
import AFTD.Kb.Tcs.ThresholdState
import AFTD.Kb.Tcs.ScheduleHistory
import AFTD.Kb.Tcs.RentOrBuyCost
import AFTD.Kb.Tcs.ThresholdSchedule

/-!
# not_threshold_schedule_competitive_ratio_two

Topic: online_algorithms   Node: b0b5620a3079

Provenance: original. Related work: refutes `threshold_schedule_competitive_ratio_two`

The statement `threshold_schedule_competitive_ratio_two` is false: The reset price `K : ℝ` is unrestricted, and for negative `K` the claim fails. Take `T = 2`, `a ≡ 0 : Fin 1 → NNReal`, `K = -1`, and the schedule `r ≡ true`.

- `schedule_history 2 a r 0 = 0` and `schedule_history 2 a r 1 = 0` (the increment is 0), so
  `rent_or_buy_cost 2 a (-1) (fun _ => true) = (0 + (-1)) + (0 + (-1)) = -2`.
- The threshold state starts at `(0,0)`, so at `t = 0` the rule buys iff `-1 ≤ 0`, i.e. `true`; then the state at `t = 1` is `(a 0, 0) = (0,0)` and it again buys. Hence `threshold_schedule 2 a (-1) ≡ true` and
  `rent_or_buy_cost 2 a (-1) (threshold_schedule 2 a (-1)) = -2`.

The required inequality then reads `-2 ≤ 2 * (-2) = -4`, which is false. This is counterexample to the theorem with no hypothesis on the sign of `K`; the published Proposition presumably assumes the reset price is nonnegative. I have verified `¬ (∀ T a K r, rent_or_buy_cost T a K (threshold_schedule T a K) ≤ 2 * rent_or_buy_cost T a K r)` in Lean.
-/

theorem not_threshold_schedule_competitive_ratio_two : ¬ (∀ (T : ℕ) (a : Fin (T - 1) → NNReal) (K : ℝ)
    (r : Fin T → Bool), rent_or_buy_cost T a K (threshold_schedule T a K) ≤ 2 * rent_or_buy_cost T a K r) := by
  intro h
  have hh := h 2 (fun _ => (0 : NNReal)) (-1) (fun _ => true)
  have e1 : rent_or_buy_cost 2 (fun _ => (0 : NNReal)) (-1) (fun _ => true) = -2 := by
    rw [rent_or_buy_cost.eq_def]
    simp only [Fin.sum_univ_two]
    rw [schedule_history.eq_def, schedule_history.eq_def]
    norm_num
  have e2 : rent_or_buy_cost 2 (fun _ => (0 : NNReal)) (-1)
      (threshold_schedule 2 (fun _ => (0 : NNReal)) (-1)) = -2 := by
    rw [rent_or_buy_cost.eq_def]
    simp only [Fin.sum_univ_two]
    rw [schedule_history.eq_def, schedule_history.eq_def]
    norm_num [threshold_schedule.eq_def, threshold_state.eq_def]
  rw [e1, e2] at hh
  norm_num at hh
