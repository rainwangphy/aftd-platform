import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.Gf8OracleSyndrome

/-!
# gf8_oracle_min_t_count

Topic: quantum   Node: 49757f0f8069

Provenance: formalization of a published result. Source: arXiv:2610.01024, Definition 18 and Fact 19

The minimal T-count of the GF(8) multiplication phase oracle on nine qubits in the Hadamard-free {CNOT, T} model, defined via the Amy-Mosca correspondence as the infimum cardinality of a parity representation of the oracle syndrome.
-/

/-- The minimal T-count of the GF(8) multiplication phase oracle in the Hadamard-free model, defined as the infimum cardinality of a parity representation of its syndrome. -/
noncomputable def gf8_oracle_min_t_count : ℕ := sInf {k : ℕ | ∃ S : Finset (Finset (Fin 9)), is_parity_repr S gf8_oracle_syndrome ∧ S.card = k}
