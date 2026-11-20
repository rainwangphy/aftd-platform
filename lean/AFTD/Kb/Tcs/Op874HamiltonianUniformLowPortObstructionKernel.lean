import AFTD.Prelude

/-!
# op874_hamiltonian_uniform_low_port_obstruction_kernel

Topic: graphs   Node: 8890a0633b67

Provenance: helper lemma. Published seven-vertex no-even-directed-cycle example, https://doi.org/10.2307/2152767, and Hamiltonian port interpretation in experiment 36120.

For the two opposite orientations of the explicitly prescribed Hamiltonian factor, every bit assignment on the seven matching edges has an edge whose two directed successor matching edges share its bit. Therefore the elementary necessary condition for exact low-port ownership with a uniform factor direction fails in both orientations; the graph-level transfer is separate.
-/

theorem op874_hamiltonian_uniform_low_port_obstruction_kernel (b : Fin 7 → Bool) : (∃ i : Fin 7, b i = b ((![3,2,5,4,5,6,2] : Fin 7 → Fin 7) i) ∧ b i = b ((![1,4,3,6,0,1,0] : Fin 7 → Fin 7) i)) ∧ (∃ i : Fin 7, b i = b ((![4,5,6,0,3,4,5] : Fin 7 → Fin 7) i) ∧ b i = b ((![6,0,1,2,1,2,3] : Fin 7 → Fin 7) i)) := by
  revert b
  decide
