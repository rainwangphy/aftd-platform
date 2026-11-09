import AFTD.Prelude

/-!
# canonical_triangle

Topic: convex_analysis   Node: 5027d6867d14

Provenance: formalization of a published result. Source: arXiv:2611.08835, equation (21)

For real parameters $a$, $b$, and $c$, the canonical triangle homothet $\triangle(a,b,c)$ is the set of points $(x,y) \in \mathbb{R}^2$ such that $a \le x$, $b \le y$, and $x+y \le c$.
-/

/-- The canonical triangle homothet Δ(a,b,c) = {(x,y) : x ≥ a, y ≥ b, x+y ≤ c}. -/
def canonical_triangle (a b c : ℝ) : Set (ℝ × ℝ) := {r : ℝ × ℝ | a ≤ r.1 ∧ b ≤ r.2 ∧ r.1 + r.2 ≤ c}
