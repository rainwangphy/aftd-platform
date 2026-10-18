import AFTD.Prelude
import AFTD.Kb.Tcs.DeadlineRequest

/-!
# IsOnlineClairvoyantScheduleGen

Topic: online_algorithms   Node: f2b829c8ca84

Provenance: formalization of a published result. Source: arXiv:2610.18767 Sec. 2

A deterministic clairvoyant online schedule generator on lists of requests produces a cache configuration at time t that depends only on the list of requests with arrival time at most t; specifically, for any two lists of deadline requests reqs₁ and reqs₂, if their sublists of requests arriving at or before t are equal, then the generator produces the same cache configuration at time t.
-/

/-- Causality condition defining a deterministic clairvoyant online schedule generator on lists of requests. -/
def IsOnlineClairvoyantScheduleGen {α : Type*}
    (Alg : List (DeadlineRequest α) → (ℕ → Finset α)) : Prop :=
  ∀ reqs₁ reqs₂ : List (DeadlineRequest α), ∀ t : ℕ,
    reqs₁.filter (fun r => r.arrival ≤ t) = reqs₂.filter (fun r => r.arrival ≤ t) →
      Alg reqs₁ t = Alg reqs₂ t
