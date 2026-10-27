import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RowLocalView
import AFTD.Kb.GameTheoryEconomics.RowProtocolSolves

/-!
# RowProblemSolvable

Topic: combinatorial_games   Node: 72d927d473ac

Provenance: formalization of a published result. Source: arXiv:2610.33032:168

The anonymous-slip puzzle for S sages in a row with n symbols and unlabeled seats (with 2 ≤ S) is solvable if there exists a protocol p : RowLocalView (Fin S) → Fin n satisfying RowProtocolSolves S hS p.
-/

/-- The anonymous-slip puzzle for `S` sages in a row with `n` symbols and unlabeled seats is solvable. -/
def RowProblemSolvable (S n : ℕ) (hS : 2 ≤ S) : Prop := ∃ p : RowLocalView (Fin S) → Fin n, RowProtocolSolves S hS p
