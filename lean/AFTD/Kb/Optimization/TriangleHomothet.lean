import AFTD.Prelude

/-!
# triangle_homothet

Topic: convex_analysis   Node: 6f4da7ad8731

Provenance: formalization of a published result. Source: arXiv:2611.08835 Section 4, eq. (22)

For points $p, q \in \mathbb{R}^2$, `triangle_homothet p q` is defined as the set of points $r \in \mathbb{R}^2$ such that $\min(p.1, q.1) \le r.1$, $\min(p.2, q.2) \le r.2$, and $r.1 + r.2 \le \max(p.1 + p.2, q.1 + q.2)$.
-/

/-- Minimal homothet of the triangle Δ containing two points p and q in ℝ². -/
def triangle_homothet (p q : ℝ × ℝ) : Set (ℝ × ℝ) := {r : ℝ × ℝ | min p.1 q.1 ≤ r.1 ∧ min p.2 q.2 ≤ r.2 ∧ r.1 + r.2 ≤ max (p.1 + p.2) (q.1 + q.2)}
