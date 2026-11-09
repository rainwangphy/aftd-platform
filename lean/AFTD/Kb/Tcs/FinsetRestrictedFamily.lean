import AFTD.Prelude

/-!
# finset_restricted_family

Topic: combinatorics   Node: 1d46833e1b47

Provenance: formalization of a published result. Source: arXiv:2611.06860, Section 2.2

Given a family of sets F and sets J and U, the restricted family F_{J,U} consists of all subsets A of J such that A ∪ U is in F.
-/

/-- The restricted family F_{J,U} = {A ⊆ J : A ∪ U ∈ F}. -/
def finset_restricted_family {α : Type*} [DecidableEq α] (ℱ : Finset (Finset α)) (J U : Finset α) : Finset (Finset α) := J.powerset.filter (fun A => A ∪ U ∈ ℱ)
