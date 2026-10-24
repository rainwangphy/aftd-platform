import AFTD.Prelude

/-!
# is_partitionable_two_complex

Topic: combinatorics   Node: 6f570b3e9dbd

Provenance: formalization of a published result. Source: arXiv:2610.27083, Section 2

A finite simplicial complex given by a set of facets is partitionable if there exists a selection map phi from facets to faces such that phi(σ) ⊆ σ for every facet σ, and every face of the complex belongs to a unique interval [phi(σ), σ].
-/

/-- A pure 2-dimensional simplicial complex is partitionable if its faces can be partitioned into boolean intervals [phi(σ), σ] indexed by its facets. -/
def is_partitionable_two_complex {V : Type*} [DecidableEq V] (facets : Finset (Finset V)) : Prop :=
  ∃ phi : Finset V → Finset V,
    (∀ σ ∈ facets, phi σ ⊆ σ) ∧
    (∀ τ ∈ facets.biUnion Finset.powerset, ∃! σ, σ ∈ facets ∧ phi σ ⊆ τ ∧ τ ⊆ σ)
