import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasConsistentEefxAlgorithm

/-!
# eefx_overestimate_threshold

Topic: fair_division   Node: 45bae31abd3a

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 7

For n agents, the error threshold is the real supremum of all error factors ρ ≥ 1 for which there exists a consistent online algorithm guaranteeing α-EEFX for some α > 0.
-/

/-- The supremum of error factors rho >= 1 admitting a consistent online algorithm guaranteeing alpha-EEFX for some alpha > 0. -/
noncomputable def eefx_overestimate_threshold (n : ℕ) : ℝ :=
  sSup {ρ : ℝ | 1 ≤ ρ ∧ has_consistent_eefx_algorithm n ρ}
