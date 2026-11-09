import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetRestrictedFamily

/-!
# finset_fiber_family

Topic: combinatorics   Node: b60398fb47a7

Provenance: formalization of a published result. Source: arXiv:2611.06860, Section 2.2

Given a family of sets F on a finite universe, a subset J, and a subset S of J, the fiber family R_{J,S} consists of all subsets U of the complement of J such that the restricted family F_{J,U} shatters S.
-/

/-- The fiber family R_{J,S} = {U ⊆ Jᶜ : S is shattered by F_{J,U}}. -/
def finset_fiber_family {α : Type*} [Fintype α] [DecidableEq α] (ℱ : Finset (Finset α)) (J S : Finset α) : Finset (Finset α) := Jᶜ.powerset.filter (fun U => (finset_restricted_family ℱ J U).Shatters S)
