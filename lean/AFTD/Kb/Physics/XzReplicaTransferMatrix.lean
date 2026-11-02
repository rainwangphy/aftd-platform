import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasisToMatrix
import AFTD.Kb.Physics.XzCyclicSucc
import AFTD.Kb.Physics.XzPauli

/-!
# xz_replica_transfer_matrix

Topic: quantum_mechanics   Node: 3d12866f75c1

Provenance: helper lemma. step towards xz_scar_uniform_reduced_spectrum_odd_length_doubling

`xz_replica_transfer_matrix q : Matrix (Fin (2*q) → Fin 2) (Fin (2*q) → Fin 2) ℂ`, with entry `∑ s, ∏ i, (xz_pauli (u i) (v i)).toMatrix (s i) (s (i+1 mod 2q))`: the trace of the product of the `2q` Pauli matrices `xz_pauli (u i) (v i)` around a cycle.
-/

/-- The q-replica transfer matrix on `2q` layers: `T_q[u,v]` is the sum over spin strings `s` of the cyclic product of local Pauli entries. -/
noncomputable def xz_replica_transfer_matrix (q : ℕ) : Matrix (Fin (2 * q) → Fin 2) (Fin (2 * q) → Fin 2) ℂ := fun u v => ∑ s : Fin (2 * q) → Fin 2, ∏ i : Fin (2 * q), (xz_pauli (u i) (v i)).toMatrix (s i) (s (xz_cyclic_succ i))
