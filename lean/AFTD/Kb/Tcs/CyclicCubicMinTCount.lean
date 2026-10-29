import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.CyclicCubicSyndrome

/-!
# cyclic_cubic_min_t_count

Topic: quantum   Node: c4874e899384

Provenance: original. Related work: arXiv:2610.01024

For a natural number n, cyclic_cubic_min_t_count n is the infimum in ℕ of the cardinalities of all parity representations S : Finset (Finset (Fin n)) of cyclic_cubic_syndrome n.
-/

/-- The minimum cardinality of a parity representation of the cyclic cubic syndrome on n qubits. -/
noncomputable def cyclic_cubic_min_t_count (n : ℕ) : ℕ := sInf {k : ℕ | ∃ S : Finset (Finset (Fin n)), is_parity_repr S (cyclic_cubic_syndrome n) ∧ S.card = k}
