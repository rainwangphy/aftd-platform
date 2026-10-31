import AFTD.Prelude
import AFTD.Kb.Tcs.AffineForm

/-!
# NcABP

Topic: algebraic_complexity   Node: e5f83215d6b8

Provenance: formalization of a published result. Source: arXiv:2610.37677, Section 1.1 and Section 3.2

An affine noncommutative algebraic branching program (ncABP) parameterized by a type F with zero and parameters m, S : ℕ consists of a source and sink in Fin S, edge weights given by AffineForm F m, and the condition that any edge with a nonzero coefficient from u to v satisfies u < v.
-/

/-- An affine noncommutative algebraic branching program (ncABP) with S vertices. -/
structure NcABP (F : Type*) [Zero F] (m S : ℕ) where
  source : Fin S
  sink : Fin S
  edge : Fin S → Fin S → AffineForm F m
  edge_lt : ∀ u v, (edge u v).c0 ≠ 0 ∨ (∃ i, (edge u v).c i ≠ 0) → u < v
