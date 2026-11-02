import AFTD.Prelude
import AFTD.Kb.Tcs.InGeneralPosition
import AFTD.Kb.Tcs.DistanceMultiplicity

/-!
# is_crescent_configuration

Topic: combinatorics   Node: 0bb28e7bb038

Provenance: formalization of a published result. Source: arXiv:2610.38368, Section 1

A finite subset S of Euclidean space ℝ^d is a crescent configuration if it is in general position and the set of its distinct pairwise distances has cardinality |S| - 1 with multiplicities 1, ..., |S| - 1.
-/

/-- A crescent configuration in d-dimensional Euclidean space is a set in general position whose distinct pairwise distances have multiplicities 1, ..., |S| - 1. -/
def is_crescent_configuration {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  in_general_position d S ∧
  ∃ D : Finset ℝ, D.card = S.card - 1 ∧
    (∀ u ∈ S.powersetCard 2, ∃ r ∈ D, ∃ x ∈ u, ∃ y ∈ u, x ≠ y ∧ dist x y = r) ∧
    D.image (distance_multiplicity S) = Finset.Icc 1 (S.card - 1)
