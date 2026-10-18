import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasibleSchedule
import AFTD.Kb.Tcs.ScheduleCost
import AFTD.Kb.Tcs.InstanceHorizon
import AFTD.Kb.Tcs.DeadlineRequest

/-!
# deadline_paging_min_cost_schedule_exists

Topic: online_algorithms   Node: 2b783746451a

Provenance: helper lemma. step towards deadline_paging_optimal_competitive_ratio_two_holes

Every feasible deadline-paging instance admits a feasible schedule whose fetch cost over the instance horizon is minimal among all feasible schedules (the offline optimum, made concrete).
-/

/-- A feasible instance has a feasible schedule of minimum fetch cost over its horizon; turns the offline optimum into a concrete schedule. -/
theorem deadline_paging_min_cost_schedule_exists
    {α : Type*} [DecidableEq α] (k : ℕ) (C₀ : Finset α) (reqs : List (DeadlineRequest α))
    (h : ∃ sched : ℕ → Finset α, IsFeasibleSchedule k C₀ sched reqs) :
    ∃ sched : ℕ → Finset α, IsFeasibleSchedule k C₀ sched reqs ∧
      ∀ sched' : ℕ → Finset α, IsFeasibleSchedule k C₀ sched' reqs →
        scheduleCost sched (instanceHorizon reqs) ≤ scheduleCost sched' (instanceHorizon reqs) := by
  classical
  obtain ⟨s₀, hs₀⟩ := h
  let P : ℕ → Prop := fun n => ∃ sched : ℕ → Finset α, IsFeasibleSchedule k C₀ sched reqs ∧ scheduleCost sched (instanceHorizon reqs) = n
  have h_ex : ∃ n, P n := ⟨scheduleCost s₀ (instanceHorizon reqs), s₀, hs₀, rfl⟩
  obtain ⟨sched, hsched_feas, hsched_cost⟩ := Nat.find_spec h_ex
  refine ⟨sched, hsched_feas, fun sched' hsched' => ?_⟩
  rw [hsched_cost]
  exact Nat.find_min' h_ex ⟨sched', hsched', rfl⟩
