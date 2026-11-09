import AFTD.Prelude

/-!
# triangle_region

Topic: convex_analysis   Node: c5d1f9a7dd92

Provenance: formalization of a published result. Source: arXiv:2611.08835 Section 4, eq. (24)

For a point $r \in \mathbb{R}^2$ and finite set $P \subset \mathbb{R}^2$, $A_0(r) = \{q \in P : r_x < q_x\}$, $A_1(r) = \{q \in P : r_y < q_y\}$, and $A_2(r) = \{q \in P : q_x + q_y < r_x + r_y\}$.
-/

/-- The three regions A₀(r), A₁(r), A₂(r) in P defined by coordinates relative to r. -/
noncomputable def triangle_region (P : Finset (ℝ × ℝ)) (r : ℝ × ℝ) (i : Fin 3) : Finset (ℝ × ℝ) := if i = 0 then P.filter (fun q : ℝ × ℝ => r.1 < q.1)
  else if i = 1 then P.filter (fun q : ℝ × ℝ => r.2 < q.2)
  else P.filter (fun q : ℝ × ℝ => q.1 + q.2 < r.1 + r.2)
