import AFTD.Prelude
import AFTD.Kb.Optimization.IsPStarKappa

/-!
# is_p_star

Topic: lp_duality   Node: f4ad3a7cccc3

Provenance: formalization of a published result. Source: scout/2611-07815-newton-steps-are-faster-for-linear-complementarity-problems.md:219

A real n-by-n matrix M indexed by Fin n belongs to the class P* if there exists a real number κ ≥ 0 such that is_p_star_kappa n M κ holds.
-/

/-- A square real matrix belongs to the class P* if it belongs to P*(κ) for some κ ≥ 0. -/
def is_p_star (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop := ∃ κ ≥ 0, is_p_star_kappa n M κ
