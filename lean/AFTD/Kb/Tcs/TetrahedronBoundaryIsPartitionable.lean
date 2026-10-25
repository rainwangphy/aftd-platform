import AFTD.Prelude
import AFTD.Kb.Tcs.IsPartitionableTwoComplex

/-!
# tetrahedron_boundary_is_partitionable

Topic: combinatorics   Node: ed009a02a9f5

Provenance: helper lemma. folklore; arXiv:2610.27083 Question 6.2

The boundary of a tetrahedron, formed by four triangular facets on four vertices, is partitionable into boolean intervals.
-/

def tetrahedron_boundary_is_partitionable_phi : Finset (Fin 4) → Finset (Fin 4)
  := fun σ => if σ = {0,1,2} then ∅ else if σ = {0,1,3} then {1,3} else if σ = {0,2,3} then {3} else if σ = {1,2,3} then {1,2,3} else ∅

/-- The boundary complex of a tetrahedron is partitionable into boolean intervals. -/
theorem tetrahedron_boundary_is_partitionable :
    is_partitionable_two_complex ({ {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3} } : Finset (Finset (Fin 4))) := by
  refine ⟨tetrahedron_boundary_is_partitionable_phi, ?_, ?_⟩
  · decide
  · have hall_exists : ∀ τ ∈ ({ {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3} } : Finset (Finset (Fin 4))).biUnion Finset.powerset,
        ∃ σ, σ ∈ ({ {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3} } : Finset (Finset (Fin 4))) ∧ tetrahedron_boundary_is_partitionable_phi σ ⊆ τ ∧ τ ⊆ σ := by decide
    have hall_unique : ∀ τ ∈ ({ {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3} } : Finset (Finset (Fin 4))).biUnion Finset.powerset,
        ∀ σ1 σ2, (σ1 ∈ ({ {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3} } : Finset (Finset (Fin 4))) ∧ tetrahedron_boundary_is_partitionable_phi σ1 ⊆ τ ∧ τ ⊆ σ1) →
          (σ2 ∈ ({ {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3} } : Finset (Finset (Fin 4))) ∧ tetrahedron_boundary_is_partitionable_phi σ2 ⊆ τ ∧ τ ⊆ σ2) → σ1 = σ2 := by decide
    intro τ hτ
    obtain ⟨σ0, hσ0⟩ := hall_exists τ hτ
    exact ⟨σ0, hσ0, fun σ hσ => hall_unique τ hτ σ σ0 hσ hσ0⟩
