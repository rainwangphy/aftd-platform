import AFTD.Prelude

/-!
# parity_bound_counterexample_state

Topic: quantum   Node: 88557d9fb6ff

Provenance: helper lemma. step towards closed_network_parity_bound_qubits

The cross-source-correlated state of the counterexample: for n = 3 sources of dimension 2 and a trivial central space (m = 1), the diagonal density matrix that puts weight 1/2 on the string (0,0,0) and weight 1/2 on the string (1,1,1).
-/

/-- Diagonal state on (Fin 3 → Fin 2) × Fin 1 with weight 1/2 on the two constant strings. -/
noncomputable def parity_bound_counterexample_state : Matrix ((Fin 3 → Fin 2) × Fin 1) ((Fin 3 → Fin 2) × Fin 1) ℂ := Matrix.diagonal (fun p => if p.1 = (fun _ => (0 : Fin 2)) then (1 / 2 : ℂ) else if p.1 = (fun _ => (1 : Fin 2)) then (1 / 2 : ℂ) else 0)
