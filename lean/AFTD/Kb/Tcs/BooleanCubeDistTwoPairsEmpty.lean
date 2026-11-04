import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanCubeDistTwoPairs
import AFTD.Kb.Tcs.TetrahedronBoundaryIsPartitionable

/-!
# boolean_cube_dist_two_pairs_empty

Topic: combinatorics   Node: 61abde4393ee

Provenance: helper lemma. folklore

For any natural number d, the number of ordered pairs at Hamming distance 2 in the empty set ∅ : Finset (Fin d → Fin 2) is 0, i.e., boolean_cube_dist_two_pairs (∅ : Finset (Fin d → Fin 2)) = 0.
-/

/-- The empty subset of the boolean cube has no pairs at Hamming distance 2. -/
theorem boolean_cube_dist_two_pairs_empty (d : ℕ) :
    boolean_cube_dist_two_pairs (∅ : Finset (Fin d → Fin 2)) = 0 := by first | exact tetrahedron_boundary_is_partitionable | (apply tetrahedron_boundary_is_partitionable <;> assumption) | (apply tetrahedron_boundary_is_partitionable <;> simp_all) | simpa using tetrahedron_boundary_is_partitionable | (simp only [boolean_cube_dist_two_pairs] at *; first | exact tetrahedron_boundary_is_partitionable | (apply tetrahedron_boundary_is_partitionable <;> assumption) | (apply tetrahedron_boundary_is_partitionable <;> simp_all) | simpa using tetrahedron_boundary_is_partitionable)
