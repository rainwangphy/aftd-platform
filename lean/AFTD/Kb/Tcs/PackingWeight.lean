import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance

/-!
# packing_weight

Topic: approximation   Node: 860c62dbb2b9

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 3

Given an instance inst of weighted k-set packing on a type α with decidable equality, the linear weight packing_weight inst A of a sub-collection A : Finset (Finset α) is the sum of inst.weight s over all s ∈ A.
-/

/-- Linear weight of a subfamily of sets. -/
def packing_weight {α : Type*} [DecidableEq α] {k : ℕ} (inst : WeightedSetPackingInstance α k) (A : Finset (Finset α)) : ℚ := ∑ s ∈ A, inst.weight s
