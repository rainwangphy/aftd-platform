import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Predecessors

/-!
# marginal_vector

Topic: general_equilibrium   Node: 06922b54f16b

Provenance: formalization of a published result. Source: arXiv:2611.16207, Section 2

For a cooperative game v : Finset α → ℝ on a finite type α with decidable equality and an ordering bijection e : Fin (Fintype.card α) ≃ α, the marginal worth vector marginal_vector v e assigns to each player i : α the value v(insert i (predecessors e i)) - v(predecessors e i).
-/

/-- The marginal worth vector of a game under ordering e. -/
def marginal_vector {α : Type*} [DecidableEq α] [Fintype α] (v : Finset α → ℝ)
    (e : Fin (Fintype.card α) ≃ α) : α → ℝ :=
  fun i => v (insert i (predecessors e i)) - v (predecessors e i)
