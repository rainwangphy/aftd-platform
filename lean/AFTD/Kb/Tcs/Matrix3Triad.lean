import AFTD.Prelude

/-!
# Matrix3Triad

Topic: algebraic_complexity   Node: eb51b56bba9c

Given a type R, a Matrix3Triad R is a structure consisting of three 3-by-3 matrices with entries in R, labeled u, v, and w.
-/

/-- A triad product for 3x3 matrices over a type R. -/
structure Matrix3Triad (R : Type*) where
  u : Matrix (Fin 3) (Fin 3) R
  v : Matrix (Fin 3) (Fin 3) R
  w : Matrix (Fin 3) (Fin 3) R
