import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliBasis

/-!
# pauliXSupport

Topic: quantum   Node: a4af24f2afc1

Provenance: helper lemma. step towards op_1254_cubic_hypergraph_fluctuation_mean_zero

The X-support (bit-flip) vector of a Pauli string: (pauliXSupport p) i = 1 iff p i ∈ {X, Y}, else 0.
-/

/-- X-support of a Pauli string, indexing the shift y = x + u in the Pauli action. -/
noncomputable def pauliXSupport {n : ℕ} (p : PauliString n) : Fin n → Fin 2 := fun i => if p i = PauliBasis.X ∨ p i = PauliBasis.Y then 1 else 0
