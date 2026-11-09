import AFTD.Prelude
import AFTD.Kb.Optimization.TriangleHomothet
import AFTD.Kb.Tcs.WeightedMaxCutLinearCombination

/-!
# triangle_homothet_mem_left

Topic: convex_analysis   Node: 9264bb35b860

Provenance: helper lemma. arXiv:2611.08835 Section 4

For points $p, q \in \mathbb{R}^2$, the point $p$ belongs to $\text{triangle\_homothet}(p, q)$.
-/

/-- Point p is contained in triangle_homothet p q. -/
theorem triangle_homothet_mem_left (p q : ℝ × ℝ) : p ∈ triangle_homothet p q := by first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination | (simp only [triangle_homothet] at *; first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination)
