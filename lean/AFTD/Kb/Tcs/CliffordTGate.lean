import AFTD.Prelude

/-!
# CliffordTGate

Topic: quantum   Node: ac096165b355

A gate of a Clifford+T circuit on N qubits: a Hadamard H on qubit i, a phase gate S on qubit i, a CNOT with control c and target t (c different from t), or a T gate on qubit i.
-/

/-- The gates of a Clifford+T circuit on N qubits: Hadamard, phase S = diag(1, i), CNOT with distinct control and target, and T = diag(1, e^{i pi/4}). -/
inductive CliffordTGate (N : ℕ) | h (i : Fin N)
  | s (i : Fin N)
  | cnot (c t : Fin N) (hct : c ≠ t)
  | t (i : Fin N)
