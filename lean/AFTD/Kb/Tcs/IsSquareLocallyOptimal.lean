import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.IsPacking
import AFTD.Kb.Tcs.SquaredWeight
import AFTD.Kb.Tcs.ConflictNeighborhood

/-!
# is_square_locally_optimal

Topic: approximation   Node: 25c6e7ddd183

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 3

Given an instance inst of weighted k-set packing on a type α with decidable equality, a packing A is square locally optimal with respect to size m exchanges (is_square_locally_optimal inst m A) if A is a packing and for every packing X in inst of cardinality at most m, the squared-weight potential of X is at most the squared-weight potential of the conflict neighborhood of X in A.
-/

/-- A packing is square-locally optimal if no exchange of size up to m increases squared weight. -/
def is_square_locally_optimal {α : Type*} [DecidableEq α] {k : ℕ} (inst : WeightedSetPackingInstance α k) (m : ℕ) (A : Finset (Finset α)) : Prop := is_packing inst A ∧ ∀ X, is_packing inst X → X.card ≤ m → squared_weight inst X ≤ squared_weight inst (conflict_neighborhood A X)
