import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunBoundary

/-!
# run_boundary_distinct

Topic: combinatorial_games   Node: 1c2d4d4f7274

Provenance: helper lemma. scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:397

The free, blocked inward, and blocked outward boundary conditions on a run in the Game of Arrows are pairwise distinct.
-/

/-- The three boundary conditions of a run are pairwise distinct. -/
theorem run_boundary_distinct :
    RunBoundary.free ≠ RunBoundary.blocked_in ∧
    RunBoundary.free ≠ RunBoundary.blocked_out ∧
    RunBoundary.blocked_in ≠ RunBoundary.blocked_out := by
  decide
