import AFTD.Prelude
import AFTD.Kb.Optimization.IsSubmodularGoalFunction

/-!
# stochastic_mst_submodular_goal_value

Topic: submodular   Node: 3df79e3754d4

Provenance: formalization of a published result. Source: scout/2610-40844-stochastic-minimum-spanning-tree-identification-with-binary.md:702

The submodular goal value Q_ID(G) of a finite graph G is the infimum in ℕ (sInf) of the set of natural numbers Q such that there exists a submodular goal function g for G with goal value Q.
-/

open scoped Classical in
/-- The minimum goal value Q of a submodular goal function for G. -/
noncomputable def stochastic_mst_submodular_goal_value {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := sInf {Q : ℕ | ∃ g, is_submodular_goal_function G g Q}
