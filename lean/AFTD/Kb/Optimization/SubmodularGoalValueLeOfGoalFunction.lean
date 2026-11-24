import AFTD.Prelude
import AFTD.Kb.Optimization.StochasticMstSubmodularGoalValue
import AFTD.Kb.Optimization.IsSubmodularGoalFunction

/-!
# submodular_goal_value_le_of_goal_function

Topic: submodular   Node: c7e967469505

Provenance: helper lemma. step towards op_853_polynomial_submodular_goal_value_bound

If g is a submodular goal function for a finite graph G with goal value Q, then the submodular goal value of G is at most Q.
-/

open scoped Classical in
/-- A submodular goal function with value Q witnesses that the infimum defining the goal value is at most Q. -/
theorem submodular_goal_value_le_of_goal_function {V : Type*} [Fintype V] (G : SimpleGraph V)
    (g : (G.edgeSet → Option Bool) → ℕ) (Q : ℕ) (h : is_submodular_goal_function G g Q) :
    stochastic_mst_submodular_goal_value G ≤ Q := by
  unfold stochastic_mst_submodular_goal_value
  exact Nat.sInf_le ⟨g, h⟩
