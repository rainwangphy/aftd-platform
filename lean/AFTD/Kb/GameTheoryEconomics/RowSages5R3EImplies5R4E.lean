import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RowProblemSolvable
import AFTD.Kb.GameTheoryEconomics.RowSolvableMono

/-!
# row_sages_5R3E_implies_5R4E

Topic: combinatorial_games   Node: 30583fea27b0

Provenance: helper lemma. arXiv:2610.33032:543

If five sages in a row with unlabeled seats can solve the anonymous-slip puzzle using three symbols (RowProblemSolvable 5 3 (by decide)), then they can also solve it using four symbols (RowProblemSolvable 5 4 (by decide)).
-/

/-- If 5R3E is solvable, then 5R4E is solvable. -/
theorem row_sages_5R3E_implies_5R4E (h : RowProblemSolvable 5 3 (by decide)) :
    RowProblemSolvable 5 4 (by decide) := by
  exact row_solvable_mono (by decide) (by decide) h
