import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance

/-!
# is_packing

Topic: approximation   Node: 6d0467a5bcd9

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 3

Given an instance inst of weighted k-set packing on a type α with decidable equality, a sub-collection A : Finset (Finset α) is a packing (is_packing inst A) if A ⊆ inst.family and the sets in A are pairwise disjoint.
-/

/-- A packing is a subfamily of pairwise disjoint sets from the instance family. -/
def is_packing {α : Type*} [DecidableEq α] {k : ℕ} (inst : WeightedSetPackingInstance α k) (A : Finset (Finset α)) : Prop := A ⊆ inst.family ∧ (A : Set (Finset α)).PairwiseDisjoint id
