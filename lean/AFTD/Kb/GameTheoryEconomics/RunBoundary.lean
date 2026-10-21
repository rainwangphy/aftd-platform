import AFTD.Prelude

/-!
# RunBoundary

Topic: combinatorial_games   Node: bb0770aba455

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:397

The boundary condition at an end of a path segment in the Game of Arrows is either free (denoted *), blocked inward (denoted →), or blocked outward (denoted ←).
-/

/-- Boundary condition of an end of a path run in the Game of Arrows: free, blocked inward, or blocked outward. -/
inductive RunBoundary : Type | free : RunBoundary
  | blocked_in : RunBoundary
  | blocked_out : RunBoundary
deriving DecidableEq, Repr
