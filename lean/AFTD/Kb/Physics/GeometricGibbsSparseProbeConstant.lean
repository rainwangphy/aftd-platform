import AFTD.Prelude
import AFTD.Kb.Physics.GeometricGibbsGoldenRatio

/-!
# geometric_gibbs_sparse_probe_constant

Topic: quantum_mechanics   Node: b2e8d4dbbe9d

Provenance: formalization of a published result. Source: arXiv:2610.35433

The asymptotic scaling constant C(q), equal to q(1-q) for q ≤ phi and (1-q)/(1+q) for phi ≤ q.
-/

/-- Conjectured two-phase asymptotic scaling constant C(q). -/
noncomputable def geometric_gibbs_sparse_probe_constant (q : ℝ) : ℝ := if q ≤ geometric_gibbs_golden_ratio then q * (1 - q) else (1 - q) / (1 + q)
