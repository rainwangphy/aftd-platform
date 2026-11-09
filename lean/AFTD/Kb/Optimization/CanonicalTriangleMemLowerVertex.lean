import AFTD.Prelude
import AFTD.Kb.Optimization.CanonicalTriangle

/-!
# canonical_triangle_mem_lower_vertex

Topic: convex_analysis   Node: f71af309d293

Provenance: helper lemma. arXiv:2611.08835, Section 4

If $a + b \le c$, then the point $(a,b)$ belongs to the canonical triangle $\triangle(a,b,c)$.
-/

/-- The lower vertex (a,b) belongs to the canonical triangle Δ(a,b,c) whenever a + b ≤ c. -/
theorem canonical_triangle_mem_lower_vertex (a b c : ℝ) (h : a + b ≤ c) :
    (a, b) ∈ canonical_triangle a b c := by
  exact ⟨le_rfl, le_rfl, h⟩
