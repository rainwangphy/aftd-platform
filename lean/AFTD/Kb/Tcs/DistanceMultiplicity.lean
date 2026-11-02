import AFTD.Prelude

/-!
# distance_multiplicity

Topic: combinatorics   Node: 8152b40a2ba4

Provenance: formalization of a published result. Source: arXiv:2610.38368, Section 1

The multiplicity of a distance r in a finite subset S of a metric space is the number of 2-element subsets of S whose two elements have distance r.
-/

open Classical in
/-- The multiplicity of a distance r among pairs of distinct points in S. -/
noncomputable def distance_multiplicity {E : Type*} [PseudoMetricSpace E]
    (S : Finset E) (r : ℝ) : ℕ :=
  ((S.powersetCard 2).filter (fun u => ∃ x ∈ u, ∃ y ∈ u, x ≠ y ∧ dist x y = r)).card
