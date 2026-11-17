import AFTD.Prelude

/-!
# parity_bound_counterexample_qubit_observable

Topic: quantum   Node: 1cb6a524f0cc

Provenance: helper lemma. step towards closed_network_parity_bound_qubits

The end-node observable family of the counterexample to `closed_network_parity_bound_qubits`: at setting y = 0 it is the Pauli Z matrix diag(1, -1), at setting y = 1 it is the identity.
-/

/-- Counterexample family: setting 0 gives Z = diag(1,-1), setting 1 gives the identity on ℂ^2. -/
def parity_bound_counterexample_qubit_observable : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun y => if y = 0 then Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else -1) else 1
