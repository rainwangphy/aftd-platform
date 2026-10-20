import AFTD.Prelude
import AFTD.Kb.Tcs.ConflictNeighborhood

/-!
# apply_repairs

Topic: approximation   Node: f8fdda5d3ef7

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 1.1

Given a type α with decidable equality, a family A : Finset (Finset α), and a collection of repairs R : Finset (Finset (Finset α)), apply_repairs A R is the union of A minus the conflict neighborhood of the union of R in A, and the union of all sets in R.
-/

/-- The packing obtained by applying a compatible family of repairs R to A. -/
def apply_repairs {α : Type*} [DecidableEq α] (A : Finset (Finset α)) (R : Finset (Finset (Finset α))) : Finset (Finset α) := (A \ conflict_neighborhood A (R.biUnion id)) ∪ (R.biUnion id)
