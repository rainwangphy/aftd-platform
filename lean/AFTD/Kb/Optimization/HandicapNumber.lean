import AFTD.Prelude
import AFTD.Kb.Optimization.IsPStarKappa

/-!
# handicap_number

Topic: lp_duality   Node: e9f48deabf41

Provenance: formalization of a published result. Source: arXiv:2611.07815 Section 1 (equation 1) and Section 2.2

The handicap number of a matrix M is the infimum of all κ ≥ 0 such that M belongs to P*(κ).
-/

/-- The handicap number of a matrix is the infimum of κ ≥ 0 such that M is in P*(κ). -/
noncomputable def handicap_number (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := sInf { κ : ℝ | is_p_star_kappa n M κ }
