import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis

/-!
# pauliPhase

Topic: quantum   Node: f34f78aeb4e3

Provenance: helper lemma. step towards op_1254_cubic_hypergraph_fluctuation_mean_zero

The coordinate-independent scalar κ(b) ∈ {1, −i} extracted from a single-qubit Pauli matrix entry: κ(Y) = −i and κ = 1 otherwise, so that σ_b(x,y) = κ(b)·[y = x + u_b]·(−1)^{z_b·x}.
-/

/-- Scalar phase in the single-qubit Pauli entry formula; |pauliPhase b| = 1. -/
noncomputable def pauliPhase : PauliBasis → ℂ := fun b => match b with | PauliBasis.I => 1 | PauliBasis.X => 1 | PauliBasis.Y => -Complex.I | PauliBasis.Z => 1
