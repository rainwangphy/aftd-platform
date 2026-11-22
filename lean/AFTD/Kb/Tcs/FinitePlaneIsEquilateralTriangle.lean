import AFTD.Prelude
import AFTD.Kb.Tcs.FinitePlaneSqNorm

/-!
# finite_plane_is_equilateral_triangle

Topic: combinatorics   Node: d16c92e95e6d

Provenance: formalization of a published result. Source: arXiv:2611.20408, Section 1, equation (1)

Three points $X, Y, Z \in \mathbb{F}_p^2$ form an equilateral triangle with nonzero squared side length if they are pairwise distinct and $\|X-Y\|^2 = \|Y-Z\|^2 = \|Z-X\|^2 \neq 0$.
-/

/-- Predicate asserting that three points in (ZMod p)^2 form an equilateral triangle with nonzero squared side length. -/
def finite_plane_is_equilateral_triangle {p : ℕ} (X Y Z : ZMod p × ZMod p) : Prop :=
  X ≠ Y ∧ Y ≠ Z ∧ Z ≠ X ∧
  finite_plane_sq_norm (X - Y) = finite_plane_sq_norm (Y - Z) ∧
  finite_plane_sq_norm (Y - Z) = finite_plane_sq_norm (Z - X) ∧
  finite_plane_sq_norm (X - Y) ≠ 0
