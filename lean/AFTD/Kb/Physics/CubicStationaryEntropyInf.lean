import AFTD.Prelude
import AFTD.Kb.Physics.CubicEdgeEntropy
import AFTD.Kb.Physics.IsStationaryCurrent
import AFTD.Kb.Physics.SimpleGraphOrientation

/-!
# cubic_stationary_entropy_inf

Topic: statistical_mechanics   Node: 861adcae1b35

Provenance: formalization of a published result. Source: arXiv:2204.00875

For 0 < J < n, S_G(J) is the infimum of sum_e phi(j_e) among stationary currents j with |j_e| < 1 and sum_e |j_e| = J.
-/

/-- Infimal stationary entropy production S_G(J) among currents with total absolute current J. -/
noncomputable def cubic_stationary_entropy_inf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (o : SimpleGraphOrientation G) (J : ℝ) : ℝ := sInf { s : ℝ | ∃ (j : G.edgeFinset → ℝ), is_stationary_current G o j ∧
    (∀ e, |j e| < 1) ∧ (∑ e, |j e| = J) ∧ (∑ e, cubic_edge_entropy (j e) = s) }
