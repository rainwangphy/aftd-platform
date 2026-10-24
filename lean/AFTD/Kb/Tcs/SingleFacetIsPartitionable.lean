import AFTD.Prelude
import AFTD.Kb.Tcs.IsPartitionableTwoComplex

/-!
# single_facet_is_partitionable

Topic: combinatorics   Node: 311a823ab27b

Provenance: helper lemma. folklore

A simplicial complex consisting of a single facet is partitionable.
-/

/-- A single simplex is partitionable into a single boolean interval [∅, σ]. -/
theorem single_facet_is_partitionable {V : Type*} [DecidableEq V] (σ : Finset V) : is_partitionable_two_complex {σ} := by
  use fun _ => ∅
  refine ⟨by simp, ?_⟩
  intro τ hτ
  rw [Finset.singleton_biUnion, Finset.mem_powerset] at hτ
  exact ⟨σ, by simp [Finset.empty_subset, hτ], fun y hy => Finset.mem_singleton.mp hy.1⟩
