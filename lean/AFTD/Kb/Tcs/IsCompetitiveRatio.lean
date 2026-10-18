import AFTD.Prelude
import AFTD.Kb.Tcs.DeadlineRequest
import AFTD.Kb.Tcs.IsFeasibleSchedule
import AFTD.Kb.Tcs.ScheduleCost
import AFTD.Kb.Tcs.InstanceHorizon
import AFTD.Kb.Tcs.IsOnlineClairvoyantScheduleGen

/-!
# IsCompetitiveRatio

Topic: online_algorithms   Node: 9380a0701845

Provenance: formalization of a published result. Source: arXiv:2610.18767 Sec. 2

A schedule generator Alg is ρ-competitive for cache capacity k and initial cache C₀ if it is online, produces a feasible schedule whenever a feasible offline schedule exists for the request list, and its total fetch cost evaluated at instanceHorizon reqs on every feasible request list is at most ρ times the fetch cost of any feasible offline schedule optSched evaluated at instanceHorizon reqs plus a constant c.
-/

/-- A deterministic online algorithm is ρ-competitive for paging with deadlines starting from initial cache C₀. -/
def IsCompetitiveRatio {α : Type*} [DecidableEq α]
    (k : ℕ) (C₀ : Finset α)
    (Alg : List (DeadlineRequest α) → (ℕ → Finset α)) (ρ : ℝ) : Prop :=
  IsOnlineClairvoyantScheduleGen Alg ∧
  (∀ reqs, (∃ opt, IsFeasibleSchedule k C₀ opt reqs) → IsFeasibleSchedule k C₀ (Alg reqs) reqs) ∧
  ∃ c : ℝ, ∀ (reqs : List (DeadlineRequest α)) (optSched : ℕ → Finset α),
    IsFeasibleSchedule k C₀ optSched reqs →
      (scheduleCost (Alg reqs) (instanceHorizon reqs) : ℝ) ≤
        ρ * (scheduleCost optSched (instanceHorizon reqs) : ℝ) + c
