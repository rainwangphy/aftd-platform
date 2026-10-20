import AFTD.Prelude

/-!
# conflict_neighborhood

Topic: approximation   Node: dd82914e6e3d

Provenance: formalization of a published result. Source: arXiv:2610.10036 Sec. 3

Given a type α with decidable equality and two finite collections of finite subsets of α, A and X (both of type Finset (Finset α)), conflict_neighborhood A X is the sub-collection of sets a ∈ A that are not disjoint from some set x ∈ X.
-/

/-- The conflict neighborhood of a family X in A: sets in A intersecting some set in X. -/
def conflict_neighborhood {α : Type*} [DecidableEq α] (A X : Finset (Finset α)) : Finset (Finset α) := A.filter (fun a => ∃ x ∈ X, ¬ Disjoint a x)
