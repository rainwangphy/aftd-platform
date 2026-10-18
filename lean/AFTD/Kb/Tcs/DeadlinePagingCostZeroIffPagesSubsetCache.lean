import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasibleSchedule
import AFTD.Kb.Tcs.ScheduleCost
import AFTD.Kb.Tcs.InstanceHorizon
import AFTD.Kb.Tcs.DeadlineRequest
import AFTD.Kb.Tcs.DeadlinePagingOptCostGePagesOutsideCache

/-!
# deadline_paging_cost_zero_iff_pages_subset_cache

Topic: online_algorithms   Node: 330b699a0cca

Provenance: helper lemma. step towards deadline_paging_optimal_competitive_ratio_two_holes

A feasible instance can be served at fetch cost zero iff every requested page is already in the initial cache.
-/

/-- Zero-cost feasibility is equivalent to all requested pages already being cached. -/
theorem deadline_paging_cost_zero_iff_pages_subset_cache
    {α : Type*} [DecidableEq α] (k : ℕ) (C₀ : Finset α) (hC₀ : C₀.card = k)
    (reqs : List (DeadlineRequest α)) :
    (∃ sched : ℕ → Finset α, IsFeasibleSchedule k C₀ sched reqs ∧
        scheduleCost sched (instanceHorizon reqs) = 0) ↔
      (reqs.map (fun r => r.page)).toFinset ⊆ C₀ := by
  constructor
  · rintro ⟨sched, hfeas, hcost⟩
    have hle := deadline_paging_opt_cost_ge_pages_outside_cache k C₀ sched reqs hfeas
    rw [hcost] at hle
    have hcard : ((reqs.map (fun r => r.page)).toFinset \ C₀).card = 0 := by omega
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcard
    exact hcard
  · intro hsub
    use fun _ => C₀
    refine ⟨⟨rfl, fun t => by rw [hC₀], fun r hr => ?_⟩, ?_⟩
    · refine ⟨r.arrival, le_rfl, r.h_deadline, ?_⟩
      apply hsub
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨r, hr, rfl⟩
    · unfold scheduleCost
      simp
