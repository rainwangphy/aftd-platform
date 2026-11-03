import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOrPower

/-!
# shannon_or_capacity

Topic: information   Node: 9e461460a88a

Provenance: formalization of a published result. Source: arXiv:2610.41977 eq. (1.1)

The Shannon OR-capacity C_OR(G) of a simple graph G is defined as the supremum over n ≥ 1 of (omega(G^{∨n}))^{1/n}, where omega denotes the clique number.
-/

/-- The Shannon OR-capacity of a simple graph. -/
noncomputable def shannon_or_capacity {V : Type*} (G : SimpleGraph V) : ℝ := ⨆ (n : ℕ) (_ : 1 ≤ n), (((simple_graph_or_power G n).cliqueNum : ℝ) ^ ((1 : ℝ) / n))
