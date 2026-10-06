import AFTD.Prelude
import AFTD.Kb.Physics.IsHamiltonianTrajectory

/-!
# is_hamiltonian_trajectory_zero

Topic: classical_mechanics   Node: 3eed057312c8

Provenance: original. Related work: machine-posed sanity check of is_hamiltonian_trajectory (zero Hamiltonian, constant trajectory); trivial, no novelty claimed

The constant zero trajectory is a Hamiltonian trajectory for the zero Hamiltonian.
-/

/-- The constant zero trajectory is a Hamiltonian trajectory for the zero Hamiltonian. -/
theorem is_hamiltonian_trajectory_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsHamiltonianTrajectory (E := E) (fun _ => 0) (fun _ => (0, 0)) := by
  simp [IsHamiltonianTrajectory]
