import AFTD.Prelude
import AFTD.Kb.Tcs.GaleDistanceGraph

/-!
# non_colorable_imp_partition_diam_gt

Topic: combinatorics   Node: 88c95365c862

Provenance: helper lemma. arXiv:2610.28828 -- A counterexample to Gale's conjecture in $\mathbb{R}^3$, Theorem 2

For every finite subset V of 3-dimensional Euclidean space and every real number t, if the distance threshold graph on V at threshold t (with edges between distinct points at distance greater than t) is not 4-colorable, then for every map c : V → Fin 4, there exists some color class whose diameter as a subset of Euclidean space is strictly greater than t.
-/

/-- If the distance threshold graph at threshold t on a finite set has no proper 4-coloring, then in every 4-coloring some color class has diameter strictly greater than t. -/
theorem non_colorable_imp_partition_diam_gt
    (V : Finset (EuclideanSpace ℝ (Fin 3))) (t : ℝ)
    (hnot : ¬ (gale_distance_graph V t).Colorable 4)
    (c : V → Fin 4) :
    ∃ i : Fin 4, t < Metric.diam ((Subtype.val : V → EuclideanSpace ℝ (Fin 3)) '' (c ⁻¹' {i})) := by
  by_contra! h
  have hc : ∀ {u v : V}, (gale_distance_graph V t).Adj u v → c u ≠ c v := by
    intro u v hadj hcuv
    have hadj' : t < dist (u : EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)) := hadj.2
    set S := (Subtype.val : V → EuclideanSpace ℝ (Fin 3)) '' (c ⁻¹' {c u})
    have huS : (u : EuclideanSpace ℝ (Fin 3)) ∈ S := ⟨u, rfl, rfl⟩
    have hvS : (v : EuclideanSpace ℝ (Fin 3)) ∈ S := ⟨v, hcuv.symm, rfl⟩
    have hbound : Bornology.IsBounded S :=
      (Set.toFinite (c ⁻¹' {c u})).image (Subtype.val : V → EuclideanSpace ℝ (Fin 3)) |>.isBounded
    have hle1 : dist (u : EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)) ≤ Metric.diam S :=
      Metric.dist_le_diam_of_mem hbound huS hvS
    have hle2 : Metric.diam S ≤ t := h (c u)
    linarith
  exact hnot ⟨SimpleGraph.Coloring.mk c hc⟩
