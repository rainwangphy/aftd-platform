import AFTD.Prelude

/-!
# scheduleCost

Topic: online_algorithms   Node: 4ffa6615e849

Provenance: formalization of a published result. Source: arXiv:2610.18767 Sec. 2

The total fetch cost of a cache schedule up to time T, defined as the sum over time steps of the number of newly fetched pages.
-/

/-- The total fetch cost of a cache schedule up to time T. -/
def scheduleCost {α : Type*} [DecidableEq α] (sched : ℕ → Finset α) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, ((sched (t + 1)) \ (sched t)).card
