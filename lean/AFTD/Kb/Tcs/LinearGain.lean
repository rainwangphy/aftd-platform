import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.PackingWeight
import AFTD.Kb.Tcs.ConflictNeighborhood

/-!
# linear_gain

Topic: approximation   Node: cafe25e20665

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 1.1

Given an instance inst of weighted k-set packing on a type α with decidable equality, the linear gain linear_gain inst A X of an exchange X with respect to A is packing_weight inst X minus packing_weight inst (conflict_neighborhood A X).
-/

/-- Linear gain of replacing the conflict neighborhood of X in A by X. -/
def linear_gain {α : Type*} [DecidableEq α] {k : ℕ} (inst : WeightedSetPackingInstance α k) (A X : Finset (Finset α)) : ℚ := packing_weight inst X - packing_weight inst (conflict_neighborhood A X)
