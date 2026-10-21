import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunGrundyAux
import AFTD.Kb.GameTheoryEconomics.RunMoveLegal
import AFTD.Kb.GameTheoryEconomics.RunGrundy
import AFTD.Kb.GameTheoryEconomics.RunBoundary
import AFTD.Kb.GameTheoryEconomics.NatMexList

/-!
# run_grundy_zero

Topic: combinatorial_games   Node: e78f3a40dced

Provenance: helper lemma. scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:441

For any boundary conditions α and β, a run of length 0 in the Game of Arrows has Grundy value 0.
-/

/-- The Grundy value of an empty run (length 0) is 0 for all boundary conditions. -/
theorem run_grundy_zero (α β : RunBoundary) :
    run_grundy 0 α β = 0 := by
  simp [run_grundy, run_grundy_aux.eq_def]
