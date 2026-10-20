import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.LinearGain

/-!
# is_repair

Topic: approximation   Node: 9e3266a125a4

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 1.1

Given an instance inst of weighted k-set packing on a type α with decidable equality, a sub-collection X : Finset (Finset α) is a repair for A (is_repair inst A X) if X is a packing in inst of cardinality at most k with strictly positive linear gain linear_gain inst A X > 0.
-/

/-- A repair is an independent set of size at most k with positive linear gain. -/
def is_repair {α : Type*} [DecidableEq α] {k : ℕ} (inst : WeightedSetPackingInstance α k) (A X : Finset (Finset α)) : Prop := is_packing inst X ∧ X.card ≤ k ∧ 0 < linear_gain inst A X
