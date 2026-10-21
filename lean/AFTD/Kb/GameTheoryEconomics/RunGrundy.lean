import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunGrundyAux
import AFTD.Kb.GameTheoryEconomics.RunBoundary

/-!
# run_grundy

Topic: combinatorial_games   Node: ca0e394e2463

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:428

The Grundy value of a run of length k with boundary conditions α and β in the Game of Arrows, defined using depth bound k + 1.
-/

/-- The Grundy value of a run of length k with boundary conditions α and β in the Game of Arrows, at canonical depth k + 1. -/
def run_grundy (k : ℕ) (α β : RunBoundary) : ℕ :=
  run_grundy_aux (k + 1) k α β
