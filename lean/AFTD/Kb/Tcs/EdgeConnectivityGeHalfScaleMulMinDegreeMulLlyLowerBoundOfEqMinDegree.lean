import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureLeTwoDivDist
import AFTD.Kb.Tcs.GraphLlyCurvatureLowerBound
import AFTD.Kb.Tcs.GraphEdgeConnectivity
import AFTD.Kb.Tcs.GraphLlyCurvature

/-!
# edge_connectivity_ge_half_scale_mul_min_degree_mul_lly_lower_bound_of_eq_minDegree

Topic: graphs   Node: b1a1a9aa3daf

Provenance: original. Related work: Partial result on OP-164 (arXiv:2610.10559, after Theorem 1.2): the bound κ_LLY(x, y) ≤ 2/d(x, y) gives (d/2) κ_LLY^(d)(G) ≤ 1, so only graphs with κ'(G) < δ(G) can fail.

OP-164 holds for every finite connected graph whose edge-connectivity equals its minimum degree: then κ'(G) ≥ (d/2) δ(G) κ_LLY^(d)(G) for every 3 ≤ d ≤ diam(G).
-/

theorem edge_connectivity_ge_half_scale_mul_min_degree_mul_lly_lower_bound_of_eq_minDegree :
    ∀ d : ℕ, 3 ≤ d → ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → d ≤ G.diam → graph_edge_connectivity G = G.minDegree →
      ((d : ℝ) / 2) * (G.minDegree : ℝ) * graph_lly_curvature_lower_bound G d ≤
        (graph_edge_connectivity G : ℝ) := by
  intro d hd V _ _ G _ hG _ heq
  rw [heq]
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : (0 : ℝ) ≤ (d : ℝ) / 2 * (G.minDegree : ℝ) := by positivity
  set S := {κ | ∃ x y : V, G.dist x y = d ∧ graph_lly_curvature G x y = κ} with hS
  have hbound : graph_lly_curvature_lower_bound G d ≤ 2 / (d : ℝ) := by
    unfold graph_lly_curvature_lower_bound
    rw [← hS]
    rcases S.eq_empty_or_nonempty with he | ⟨κ, x, y, hxy, rfl⟩
    · rw [he, Real.sInf_empty]; positivity
    · have hfin : S.Finite := by
        have : S ⊆ Set.range (fun p : V × V => graph_lly_curvature G p.1 p.2) := by
          rintro _ ⟨a, b, -, rfl⟩; exact ⟨(a, b), rfl⟩
        exact (Set.finite_range _).subset this
      have hne : x ≠ y := by
        rintro rfl; simp at hxy; omega
      calc sInf S ≤ graph_lly_curvature G x y := csInf_le hfin.bddBelow ⟨x, y, hxy, rfl⟩
        _ ≤ 2 / (G.dist x y : ℝ) := graph_lly_curvature_le_two_div_dist G hG x y hne
        _ = 2 / (d : ℝ) := by rw [hxy]
  calc (d : ℝ) / 2 * (G.minDegree : ℝ) * graph_lly_curvature_lower_bound G d
      ≤ (d : ℝ) / 2 * (G.minDegree : ℝ) * (2 / (d : ℝ)) := mul_le_mul_of_nonneg_left hbound hc
    _ = G.minDegree := by field_simp
