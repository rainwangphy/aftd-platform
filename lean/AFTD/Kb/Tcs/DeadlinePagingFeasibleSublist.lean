import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasibleSchedule
import AFTD.Kb.Tcs.DeadlineRequest

/-!
# deadline_paging_feasible_sublist

Topic: online_algorithms   Node: 7e380c7e45fc

Provenance: helper lemma. step towards deadline_paging_optimal_competitive_ratio_two_holes

Feasibility of a schedule for a request list passes to any sublist of the requests.
-/

/-- Feasibility is inherited by sublists, hence in particular by arrival prefixes. -/
theorem deadline_paging_feasible_sublist
    {α : Type*} [DecidableEq α] (k : ℕ) (C₀ : Finset α) (sched : ℕ → Finset α)
    {reqs reqs' : List (DeadlineRequest α)} (hsub : reqs' ⊆ reqs)
    (h : IsFeasibleSchedule k C₀ sched reqs) :
    IsFeasibleSchedule k C₀ sched reqs' := ⟨h.1, h.2.1, fun r hr => h.2.2 r (hsub hr)⟩
