import AFTD.Prelude
import AFTD.Kb.Tcs.DeadlineRequest

/-!
# IsFeasibleSchedule

Topic: online_algorithms   Node: bd3fc224f1cd

Provenance: formalization of a published result. Source: arXiv:2610.18767 Sec. 2

A schedule of cache configurations of size at most k is feasible for a list of deadline requests starting from initial cache C₀ if it starts at C₀, keeps cache size at most k at all times, and caches each requested page at some time between its arrival and deadline.
-/

/-- Feasibility of a cache schedule for an instance of paging with deadlines. -/
def IsFeasibleSchedule {α : Type*} (k : ℕ) (C₀ : Finset α)
    (sched : ℕ → Finset α) (reqs : List (DeadlineRequest α)) : Prop :=
  sched 0 = C₀ ∧
  (∀ t, (sched t).card ≤ k) ∧
  (∀ r ∈ reqs, ∃ t, r.arrival ≤ t ∧ t ≤ r.deadline ∧ r.page ∈ sched t)
