import AFTD.Prelude
import AFTD.Kb.Optimization.SsssPrimalFeasible
import AFTD.Kb.Optimization.SsssPrimalObj

/-!
# ssss_is_primal_opt_val

Topic: lp_duality   Node: ea897dd5ed0f

Provenance: formalization of a published result. Source: arXiv:2611.26188, Section 3

A real number LP is the optimal value of the LP relaxation (SSSS-P) for an edge set E : Finset (V × V), edge costs c : V × V → ℝ, terminals s, t ∈ V, and integer k : ℕ if there exists a primal feasible solution x : V × V → ℝ with ssss_primal_obj E c x = LP, and every primal feasible solution x' satisfies LP ≤ ssss_primal_obj E c x'.
-/

/-- A real number LP is the optimal value of the primal LP relaxation (SSSS-P) for k paths. -/
def ssss_is_primal_opt_val {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (c : V × V → ℝ) (s t : V) (k : ℕ) (LP : ℝ) : Prop :=
  (∃ x, ssss_primal_feasible E s t k x ∧ ssss_primal_obj E c x = LP) ∧
  (∀ x, ssss_primal_feasible E s t k x → LP ≤ ssss_primal_obj E c x)
