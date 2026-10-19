import AFTD.Prelude

/-!
# SpiderTree

Topic: combinatorial_games   Node: 981b03ea76af

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md, Section 2.2

The structure SpiderTree consists of three natural number fields x : ℕ, y : ℕ, and z : ℕ, recording the parameters of a 3-legged spider tree.
-/

/-- A structure SpiderTree recording the three leg parameters x, y, z : ℕ of a 3-legged spider. -/
structure SpiderTree where
  x : ℕ
  y : ℕ
  z : ℕ
  deriving DecidableEq, Repr
