import AFTD.Prelude
import AFTD.Kb.Tcs.CliffordTCircuitTCount
import AFTD.Kb.Tcs.CliffordTGate

/-!
# clifford_t_circuit_t_count_example

Topic: quantum   Node: d045c2b3a235

Sanity check: the circuit H_0, T_0, T_1 on two qubits has T-count 2.
-/

theorem clifford_t_circuit_t_count_example : clifford_t_circuit_t_count ([.h 0, .t 0, .t 1] : List (CliffordTGate 2)) = 2 := by decide
