import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance

/-!
# squared_weight

Topic: approximation   Node: 651afbfd9c01

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 3

Given an instance inst of weighted k-set packing on a type α with decidable equality, the squared-weight potential squared_weight inst A of a sub-collection A : Finset (Finset α) is the sum of (inst.weight s)^2 over all s ∈ A.
-/

/-- Squared-weight potential of a subfamily of sets. -/
def squared_weight {α : Type*} [DecidableEq α] {k : ℕ} (inst : WeightedSetPackingInstance α k) (A : Finset (Finset α)) : ℚ := ∑ s ∈ A, (inst.weight s) ^ 2
