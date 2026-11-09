import AFTD.Prelude
import AFTD.Kb.Optimization.TriangleRegion

/-!
# triangle_region_inter_three_empty

Topic: convex_analysis   Node: 8af624724b12

Provenance: helper lemma. arXiv:2611.08835 Section 4, Lemma 8 proof

For any finite set $P \subset \mathbb{R}^2$ and point $r \in \mathbb{R}^2$, the intersection $A_0(r) \cap A_1(r) \cap A_2(r)$ is empty.
-/

/-- The three-fold intersection of A₀(r), A₁(r), A₂(r) is empty. -/
theorem triangle_region_inter_three_empty (P : Finset (ℝ × ℝ)) (r : ℝ × ℝ) :
    triangle_region P r 0 ∩ triangle_region P r 1 ∩ triangle_region P r 2 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Finset.mem_inter, Finset.mem_inter] at hq
  rcases hq with ⟨⟨h0, h1⟩, h2⟩
  dsimp [triangle_region] at h0 h1 h2
  rw [Finset.mem_filter] at h0 h1 h2
  rcases h0 with ⟨-, h0⟩
  rcases h1 with ⟨-, h1⟩
  rcases h2 with ⟨-, h2⟩
  linarith
