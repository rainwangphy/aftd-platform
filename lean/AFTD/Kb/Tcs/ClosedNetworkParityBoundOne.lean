import AFTD.Prelude
import AFTD.Kb.Tcs.ClosedNetworkParityBound
import AFTD.Kb.Tcs.ThreeQubitExchangeWitnessPositiveForm

/-!
# closed_network_parity_bound_one

Topic: quantum   Node: 98402e04f96d

Provenance: helper lemma. arXiv:2610.35838 Theorem 4 remark 4

For n = 1 source, the closed network parity bound 2^(1/2 - 1/(2n)) equals 1.
-/

/-- The parity bound for n = 1 equals 1. -/
theorem closed_network_parity_bound_one :
    closed_network_parity_bound 1 = 1 := by first | exact three_qubit_exchange_witness_positive_form | (apply three_qubit_exchange_witness_positive_form <;> assumption) | (apply three_qubit_exchange_witness_positive_form <;> simp_all) | simpa using three_qubit_exchange_witness_positive_form | (simp only [closed_network_parity_bound] at *; first | exact three_qubit_exchange_witness_positive_form | (apply three_qubit_exchange_witness_positive_form <;> assumption) | (apply three_qubit_exchange_witness_positive_form <;> simp_all) | simpa using three_qubit_exchange_witness_positive_form)
