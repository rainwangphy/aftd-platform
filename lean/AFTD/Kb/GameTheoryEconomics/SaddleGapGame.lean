import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame

/-!
# saddle_gap_game

Topic: equilibria   Node: c2190deb18ca

Provenance: formalization of a published result. Source: arXiv:2610.25524 Section 4

Given an n-by-n payoff matrix A, the saddle-gap game S has row player choosing a pair (i, j) in [n]² and column player choosing k in [n], with payoff A_{ik} - A_{kj}.
-/

/-- The saddle-gap auxiliary zero-sum matrix game S for a matrix A. -/
def saddle_gap_game {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : MatrixGame (Fin n × Fin n) (Fin n) ℝ := ⟨fun (i, j) k => A i k - A k j⟩
