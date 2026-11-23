import AFTD.Prelude

/-!
# PowerRelation

Topic: social_choice   Node: edcc06727a05

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 1

A power relation is a weak order on a finite collection of feasible coalitions of individuals, represented by an ordered partition into non-empty, pairwise disjoint equivalence classes from highest to lowest rank.
-/

/-- A power relation on a finite set of feasible coalitions of individuals, represented by its ordered equivalence classes from best to worst. -/
structure PowerRelation (X : Type*) where
  classes : List (Finset (Finset X))
  classes_nonempty : ∀ c ∈ classes, (c : Finset (Finset X)).Nonempty
  classes_disjoint : classes.Pairwise Disjoint
