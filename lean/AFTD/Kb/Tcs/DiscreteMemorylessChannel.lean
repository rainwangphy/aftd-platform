import AFTD.Prelude

/-!
# DiscreteMemorylessChannel

Topic: information   Node: 98baddf360fe

Provenance: formalization of a published result. Source: arXiv:2610.41977, Section 5; Shannon 1956

A discrete memoryless channel from input alphabet A to finite output alphabet Y is defined by non-negative transition probabilities summing to 1 for each input symbol.
-/

/-- A discrete memoryless channel from input alphabet A to finite output alphabet Y specified by transition probabilities. -/
structure DiscreteMemorylessChannel (A Y : Type*) [Fintype Y] where
  prob : A → Y → ℝ
  prob_nonneg : ∀ a y, 0 ≤ prob a y
  prob_sum : ∀ a, ∑ y, prob a y = 1
