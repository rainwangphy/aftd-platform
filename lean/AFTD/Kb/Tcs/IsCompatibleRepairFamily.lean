import AFTD.Prelude

/-!
# is_compatible_repair_family

Topic: approximation   Node: 368fa444a7b8

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 1.1

For a type α with decidable equality, a finite collection of repairs R : Finset (Finset (Finset α)) is compatible (is_compatible_repair_family R) if the union of all sets appearing in repairs in R (as a subset of Finset α) is pairwise disjoint.
-/

/-- A family of repairs is compatible if their constituent sets are pairwise disjoint. -/
def is_compatible_repair_family {α : Type*} [DecidableEq α] (R : Finset (Finset (Finset α))) : Prop := (R.biUnion id : Set (Finset α)).PairwiseDisjoint id
