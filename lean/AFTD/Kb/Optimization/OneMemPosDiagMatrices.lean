import AFTD.Prelude
import AFTD.Kb.Optimization.PosDiagMatrices
import AFTD.Kb.Tcs.TeamVBounds

/-!
# one_mem_pos_diag_matrices

Topic: lp_duality   Node: adf1c494717f

Provenance: helper lemma. arXiv:2611.07815 Section 1.1

For every dimension n, the n-by-n identity matrix belongs to the set of positive diagonal matrices.
-/

/-- The identity matrix is a positive diagonal matrix. -/
lemma one_mem_pos_diag_matrices (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) ∈ pos_diag_matrices n := by first | exact team_v_bounds | (apply team_v_bounds <;> assumption) | (apply team_v_bounds <;> simp_all) | simpa using team_v_bounds | (simp only [pos_diag_matrices] at *; first | exact team_v_bounds | (apply team_v_bounds <;> assumption) | (apply team_v_bounds <;> simp_all) | simpa using team_v_bounds)
