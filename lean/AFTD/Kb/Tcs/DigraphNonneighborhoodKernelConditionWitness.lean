import AFTD.Prelude

/-!
# digraph_nonneighborhood_kernel_condition_witness

Topic: graphs   Node: b93e37c8d2e1

Provenance: helper lemma. Finite witness for the non-neighborhood-kernel condition, audited in experiments 14445, 14447 and 14448. No novelty is claimed.

The displayed source-free oriented eight-vertex graph has a singleton kernel in every non-neighborhood and no kernel of its own; it contains a five-clique, and the complement of every tournament vertex set contains a directed triangle.
-/

set_option maxRecDepth 50000
set_option maxHeartbeats 50000000

def in541_local_example_out (v : Fin 8) : Finset (Fin 8) :=
  if v = 0 then {4,6} else if v = 1 then {2,3,4} else
  if v = 2 then {0,5} else if v = 3 then {2,7} else
  if v = 4 then {3,7} else if v = 5 then {1,3,4,6,7} else
  if v = 6 then {1,2} else {0,1}

def in541_local_example_independent (K : Finset (Fin 8)) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, u ≠ v → v ∉ in541_local_example_out u

instance (K : Finset (Fin 8)) : Decidable (in541_local_example_independent K) := by
  unfold in541_local_example_independent
  infer_instance

theorem digraph_nonneighborhood_kernel_condition_witness :
    (∀ v, v ∉ in541_local_example_out v) ∧
    (∀ u v, v ∈ in541_local_example_out u → u ∉ in541_local_example_out v) ∧
    (∀ v, ∃ u, v ∈ in541_local_example_out u) ∧
    (∀ v, ∃ k, k ≠ v ∧ k ∉ in541_local_example_out v ∧
      v ∉ in541_local_example_out k ∧
      ∀ x, x ≠ v → x ∉ in541_local_example_out v →
        v ∉ in541_local_example_out x → x = k ∨ x ∈ in541_local_example_out k) ∧
    (∀ K : Finset (Fin 8), in541_local_example_independent K →
      ¬ (∀ v, ∃ u ∈ K, u = v ∨ v ∈ in541_local_example_out u)) ∧
    (∀ u ∈ ({1,3,4,5,7} : Finset (Fin 8)),
      ∀ v ∈ ({1,3,4,5,7} : Finset (Fin 8)), u ≠ v →
        v ∈ in541_local_example_out u ∨ u ∈ in541_local_example_out v) ∧
    (∀ T : Finset (Fin 8),
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v →
        v ∈ in541_local_example_out u ∨ u ∈ in541_local_example_out v) →
      ∃ a b c, a ∉ T ∧ b ∉ T ∧ c ∉ T ∧
        b ∈ in541_local_example_out a ∧ c ∈ in541_local_example_out b ∧
        a ∈ in541_local_example_out c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
