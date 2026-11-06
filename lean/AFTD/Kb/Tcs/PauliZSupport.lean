import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliBasis

/-!
# pauliZSupport

Topic: quantum   Node: b26e5cfdd755

Provenance: helper lemma. step towards op_1254_cubic_hypergraph_fluctuation_mean_zero

The Z-support (phase) vector of a Pauli string: (pauliZSupport p) i = 1 iff p i ∈ {Y, Z}, else 0.
-/

/-- Z-support of a Pauli string, giving the character (−1)^{z·x}. -/
noncomputable def pauliZSupport {n : ℕ} (p : PauliString n) : Fin n → Fin 2 := fun i => if p i = PauliBasis.Y ∨ p i = PauliBasis.Z then 1 else 0
