import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg

/-!
# five_vertex_min_degree_two_idle_coupling_bound

Topic: graphs   Node: f38b2e54e9a3

Provenance: helper lemma. step towards five_vertex_min_degree_two_wasserstein_lt_one

In any 5-vertex graph with minimum degree at least 2 and adjacent vertices x and y, the idle measures at α = 1/2 satisfy 1 < 2 S0 + m_xy.
-/

lemma five_vertex_min_degree_two_idle_coupling_bound_idle_eval_common {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    let μ := graph_idle_measure G (1 / 2) x
    let ν := graph_idle_measure G (1 / 2) y
    μ z = 1 / (2 * (G.degree x : ℝ)) ∧
    ν z = 1 / (2 * (G.degree y : ℝ)) := by
  intro μ ν
  have hzx : z ≠ x := hxz.ne.symm
  have hzy : z ≠ y := hyz.ne.symm
  dsimp [μ, ν, graph_idle_measure]
  simp only [hzx, hzy, hxz, hyz, ↓reduceIte]
  refine ⟨by ring, by ring⟩

lemma five_vertex_min_degree_two_idle_coupling_bound_min_eval_xy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hδ : 2 ≤ G.minDegree) (x y : V) (hxy : G.Adj x y) :
    let μ := graph_idle_measure G (1 / 2) x
    let ν := graph_idle_measure G (1 / 2) y
    min (μ x) (ν x) = 1 / (2 * (G.degree y : ℝ)) ∧
    min (μ y) (ν y) = 1 / (2 * (G.degree x : ℝ)) ∧
    μ x - min (μ x) (ν x) = 1 / 2 - 1 / (2 * (G.degree y : ℝ)) ∧
    ν y - min (μ y) (ν y) = 1 / 2 - 1 / (2 * (G.degree x : ℝ)) := by
  intro μ ν
  have hne : x ≠ y := hxy.ne
  have hne' : y ≠ x := hne.symm
  have hyx : G.Adj y x := hxy.symm
  have hdegx : 2 ≤ G.degree x := le_trans hδ (SimpleGraph.minDegree_le_degree G x)
  have hdegy : 2 ≤ G.degree y := le_trans hδ (SimpleGraph.minDegree_le_degree G y)
  have hμx : μ x = 1 / 2 := by
    dsimp [μ, graph_idle_measure]; simp
  have hμy : μ y = 1 / (2 * (G.degree x : ℝ)) := by
    dsimp [μ, graph_idle_measure]; simp [hne', hxy]; ring
  have hνy : ν y = 1 / 2 := by
    dsimp [ν, graph_idle_measure]; simp
  have hνx : ν x = 1 / (2 * (G.degree y : ℝ)) := by
    dsimp [ν, graph_idle_measure]; simp [hne, hyx]; ring
  have hle_x : ν x ≤ μ x := by
    rw [hνx, hμx]
    have : (1 : ℝ) / (2 * ↑(G.degree y)) ≤ 1 / (2 * 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (2 : ℝ) ≤ (G.degree y : ℝ) := by exact_mod_cast hdegy
      linarith
    linarith
  have hle_y : μ y ≤ ν y := by
    rw [hμy, hνy]
    have : (1 : ℝ) / (2 * ↑(G.degree x)) ≤ 1 / (2 * 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (2 : ℝ) ≤ (G.degree x : ℝ) := by exact_mod_cast hdegx
      linarith
    linarith
  have hmin_x : min (μ x) (ν x) = ν x := min_eq_right hle_x
  have hmin_y : min (μ y) (ν y) = μ y := min_eq_left hle_y
  refine ⟨by rw [hmin_x, hνx], by rw [hmin_y, hμy], by rw [hmin_x, hμx, hνx], by rw [hmin_y, hνy, hμy]⟩

lemma five_vertex_min_degree_two_idle_coupling_bound_sum_triple_le_S0 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let μ := graph_idle_measure G (1 / 2) x
    let ν := graph_idle_measure G (1 / 2) y
    let S0 := ∑ v, min (μ v) (ν v)
    min (μ x) (ν x) + min (μ y) (ν y) + min (μ z) (ν z) ≤ S0 := by
  intro μ ν S0
  have h_nonneg : ∀ i : V, 0 ≤ min (μ i) (ν i) := by
    intro i
    have hμ : 0 ≤ μ i := graph_idle_measure_nonneg G (1/2) (by norm_num) (by norm_num) x i
    have hν : 0 ≤ ν i := graph_idle_measure_nonneg G (1/2) (by norm_num) (by norm_num) y i
    exact le_min hμ hν
  have h := Finset.sum_le_univ_sum_of_nonneg (s := {x, y, z}) h_nonneg
  have hx : x ∉ ({y, z} : Finset V) := by simp [hxy, hxz]
  have hy : y ∉ ({z} : Finset V) := by simp [hyz]
  rw [Finset.sum_insert hx, Finset.sum_insert hy, Finset.sum_singleton] at h
  linarith

lemma five_vertex_min_degree_two_idle_coupling_bound_sum_pair_le_S0 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : x ≠ y) :
    let μ := graph_idle_measure G (1 / 2) x
    let ν := graph_idle_measure G (1 / 2) y
    let S0 := ∑ v, min (μ v) (ν v)
    min (μ x) (ν x) + min (μ y) (ν y) ≤ S0 := by
  intro μ ν S0
  have h_nonneg : ∀ i : V, 0 ≤ min (μ i) (ν i) := by
    intro i
    have hμ : 0 ≤ μ i := graph_idle_measure_nonneg G (1/2) (by norm_num) (by norm_num) x i
    have hν : 0 ≤ ν i := graph_idle_measure_nonneg G (1/2) (by norm_num) (by norm_num) y i
    exact le_min hμ hν
  have h := Finset.sum_le_univ_sum_of_nonneg (s := {x, y}) h_nonneg
  have hx : x ∉ ({y} : Finset V) := by simp [hxy]
  rw [Finset.sum_insert hx, Finset.sum_singleton] at h
  linarith

lemma five_vertex_min_degree_two_idle_coupling_bound_case1_arith (dx dy : ℝ) (hx2 : 2 ≤ dx) (hx4 : dx ≤ 4) (hy2 : 2 ≤ dy) (hy4 : dy ≤ 4) :
    1 < 1 / dy + 1 / dx + 2 * min (1 / (2 * dx)) (1 / (2 * dy)) +
        min (1 / 2 - 1 / (2 * dy)) (1 / 2 - 1 / (2 * dx)) := by
  rcases le_total dx dy with hle | hle
  · have h1 : min (1 / (2 * dx)) (1 / (2 * dy)) = 1 / (2 * dy) := by
      apply min_eq_right
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
      linarith
    have h2 : min (1 / 2 - 1 / (2 * dy)) (1 / 2 - 1 / (2 * dx)) = 1 / 2 - 1 / (2 * dx) := by
      apply min_eq_right
      have : 1 / (2 * dy) ≤ 1 / (2 * dx) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
        linarith
      linarith
    rw [h1, h2]
    have : (1 : ℝ) / dy + 1 / dx + 2 * (1 / (2 * dy)) + (1 / 2 - 1 / (2 * dx)) =
           1 / 2 + 2 / dy + 1 / (2 * dx) := by ring
    rw [this]
    have hdy : 2 / dy ≥ 2 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hy4
    have hdx : 1 / (2 * dx) > 0 := by positivity
    linarith
  · have h1 : min (1 / (2 * dx)) (1 / (2 * dy)) = 1 / (2 * dx) := by
      apply min_eq_left
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
      linarith
    have h2 : min (1 / 2 - 1 / (2 * dy)) (1 / 2 - 1 / (2 * dx)) = 1 / 2 - 1 / (2 * dy) := by
      apply min_eq_left
      have : 1 / (2 * dx) ≤ 1 / (2 * dy) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
        linarith
      linarith
    rw [h1, h2]
    have : (1 : ℝ) / dy + 1 / dx + 2 * (1 / (2 * dx)) + (1 / 2 - 1 / (2 * dy)) =
           1 / 2 + 2 / dx + 1 / (2 * dy) := by ring
    rw [this]
    have hdx : 2 / dx ≥ 2 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hx4
    have hdy : 1 / (2 * dy) > 0 := by positivity
    linarith

lemma five_vertex_min_degree_two_idle_coupling_bound_case2_arith (nx ny : ℕ) (hx2 : 2 ≤ nx) (hy2 : 2 ≤ ny) (hsum : nx + ny ≤ 5) :
    let dx : ℝ := nx
    let dy : ℝ := ny
    1 < 1 / dy + 1 / dx + min (1 / 2 - 1 / (2 * dy)) (1 / 2 - 1 / (2 * dx)) := by
  intro dx dy
  have hx2_r : (2 : ℝ) ≤ (nx : ℝ) := by exact_mod_cast hx2
  have hy2_r : (2 : ℝ) ≤ (ny : ℝ) := by exact_mod_cast hy2
  rcases le_total nx ny with hle | hle
  · have hx_le : nx ≤ 2 := by omega
    have hx_eq : nx = 2 := by omega
    have hy_le : ny ≤ 3 := by omega
    have hx : dx = 2 := by
      show (nx : ℝ) = 2; exact_mod_cast hx_eq
    have hy : dy ≤ 3 := by
      show (ny : ℝ) ≤ 3; exact_mod_cast hy_le
    have hdx_le_dy : dx ≤ dy := by
      show (nx : ℝ) ≤ (ny : ℝ); exact_mod_cast hle
    have h2 : min (1 / 2 - 1 / (2 * dy)) (1 / 2 - 1 / (2 * dx)) = 1 / 2 - 1 / (2 * dx) := by
      apply min_eq_right
      have : 1 / (2 * dy) ≤ 1 / (2 * dx) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
        linarith
      linarith
    rw [h2, hx]
    have : (1 : ℝ) / dy + 1 / 2 + (1 / 2 - 1 / (2 * 2)) = 3 / 4 + 1 / dy := by ring
    rw [this]
    have hdy : 1 / dy ≥ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hy
    linarith
  · have hy_le : ny ≤ 2 := by omega
    have hy_eq : ny = 2 := by omega
    have hx_le : nx ≤ 3 := by omega
    have hy : dy = 2 := by
      show (ny : ℝ) = 2; exact_mod_cast hy_eq
    have hx : dx ≤ 3 := by
      show (nx : ℝ) ≤ 3; exact_mod_cast hx_le
    have hdy_le_dx : dy ≤ dx := by
      show (ny : ℝ) ≤ (nx : ℝ); exact_mod_cast hle
    have h2 : min (1 / 2 - 1 / (2 * dy)) (1 / 2 - 1 / (2 * dx)) = 1 / 2 - 1 / (2 * dy) := by
      apply min_eq_left
      have : 1 / (2 * dx) ≤ 1 / (2 * dy) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
        linarith
      linarith
    rw [h2, hy]
    have : (1 : ℝ) / 2 + 1 / dx + (1 / 2 - 1 / (2 * 2)) = 3 / 4 + 1 / dx := by ring
    rw [this]
    have hdx : 1 / dx ≥ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hx
    linarith

/-- Lower bound 1 < 2 S₀ + m_xy for idle measures at α = 1/2 on 5-vertex graphs of minimum degree at least 2. -/
theorem five_vertex_min_degree_two_idle_coupling_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 5)
    (hδ : 2 ≤ G.minDegree) (x y : V) (hxy : G.Adj x y) :
    let μ := graph_idle_measure G (1 / 2) x
    let ν := graph_idle_measure G (1 / 2) y
    let S0 := ∑ v, min (μ v) (ν v)
    let μ1 (a : V) := μ a - min (μ a) (ν a)
    let ν1 (b : V) := ν b - min (μ b) (ν b)
    let m_xy := min (μ1 x) (ν1 y)
    1 < 2 * S0 + m_xy := by
  intro μ ν S0 μ1 ν1 m_xy
  have hne : x ≠ y := hxy.ne
  have hdegx_ge2 : 2 ≤ G.degree x := le_trans hδ (SimpleGraph.minDegree_le_degree G x)
  have hdegy_ge2 : 2 ≤ G.degree y := le_trans hδ (SimpleGraph.minDegree_le_degree G y)
  have hdegx_le4 : G.degree x ≤ 4 := by
    have := G.degree_lt_card_verts x
    omega
  have hdegy_le4 : G.degree y ≤ 4 := by
    have := G.degree_lt_card_verts y
    omega
  have hdx2_r : (2 : ℝ) ≤ (G.degree x : ℝ) := by exact_mod_cast hdegx_ge2
  have hdy2_r : (2 : ℝ) ≤ (G.degree y : ℝ) := by exact_mod_cast hdegy_ge2
  have hdx4_r : (G.degree x : ℝ) ≤ 4 := by exact_mod_cast hdegx_le4
  have hdy4_r : (G.degree y : ℝ) ≤ 4 := by exact_mod_cast hdegy_le4
  have hmin_xy := five_vertex_min_degree_two_idle_coupling_bound_min_eval_xy G hδ x y hxy
  have hm_xy_eq : m_xy = min (1 / 2 - 1 / (2 * (G.degree y : ℝ))) (1 / 2 - 1 / (2 * (G.degree x : ℝ))) := by
    dsimp [m_xy, μ1, ν1]
    rw [hmin_xy.2.2.1, hmin_xy.2.2.2]
  by_cases hdisj : Disjoint (G.neighborFinset x) (G.neighborFinset y)
  · -- Case 2: disjoint neighbors
    have hunion : (G.neighborFinset x ∪ G.neighborFinset y).card = G.degree x + G.degree y := by
      rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset x ∪ G.neighborFinset y ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard, hunion] at hle
    have hS0_ge : 1 / (2 * (G.degree y : ℝ)) + 1 / (2 * (G.degree x : ℝ)) ≤ S0 := by
      have hpair := five_vertex_min_degree_two_idle_coupling_bound_sum_pair_le_S0 G x y hne
      dsimp [μ, ν, S0] at hpair
      rw [hmin_xy.1, hmin_xy.2.1] at hpair
      exact hpair
    have h2S0 : 1 / (G.degree y : ℝ) + 1 / (G.degree x : ℝ) ≤ 2 * S0 := by
      have : 1 / (G.degree y : ℝ) + 1 / (G.degree x : ℝ) =
          2 * (1 / (2 * (G.degree y : ℝ)) + 1 / (2 * (G.degree x : ℝ))) := by ring
      linarith
    have hbound := five_vertex_min_degree_two_idle_coupling_bound_case2_arith (G.degree x) (G.degree y) hdegx_ge2 hdegy_ge2 hle
    dsimp at hbound
    rw [hm_xy_eq]
    linarith
  · -- Case 1: common neighbor exists
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    have hnonempty : (G.neighborFinset x ∩ G.neighborFinset y).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hdisj
    rcases hnonempty with ⟨z, hz⟩
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hz
    have hxz : G.Adj x z := hz.1
    have hyz : G.Adj y z := hz.2
    have hzx : z ≠ x := hxz.ne.symm
    have hzy : z ≠ y := hyz.ne.symm
    have hx_ne_z : x ≠ z := hxz.ne
    have hy_ne_z : y ≠ z := hyz.ne
    have hcommon := five_vertex_min_degree_two_idle_coupling_bound_idle_eval_common G x y z hxz hyz
    have hS0_ge : 1 / (2 * (G.degree y : ℝ)) + 1 / (2 * (G.degree x : ℝ)) +
        min (1 / (2 * (G.degree x : ℝ))) (1 / (2 * (G.degree y : ℝ))) ≤ S0 := by
      have htriple := five_vertex_min_degree_two_idle_coupling_bound_sum_triple_le_S0 G x y z hne hx_ne_z hy_ne_z
      dsimp [μ, ν, S0] at htriple
      rw [hmin_xy.1, hmin_xy.2.1, hcommon.1, hcommon.2] at htriple
      exact htriple
    have h2S0 : 1 / (G.degree y : ℝ) + 1 / (G.degree x : ℝ) +
        2 * min (1 / (2 * (G.degree x : ℝ))) (1 / (2 * (G.degree y : ℝ))) ≤ 2 * S0 := by
      have : 1 / (G.degree y : ℝ) + 1 / (G.degree x : ℝ) +
          2 * min (1 / (2 * (G.degree x : ℝ))) (1 / (2 * (G.degree y : ℝ))) =
          2 * (1 / (2 * (G.degree y : ℝ)) + 1 / (2 * (G.degree x : ℝ)) +
               min (1 / (2 * (G.degree x : ℝ))) (1 / (2 * (G.degree y : ℝ)))) := by ring
      linarith
    have hbound := five_vertex_min_degree_two_idle_coupling_bound_case1_arith (G.degree x : ℝ) (G.degree y : ℝ)
        hdx2_r hdx4_r hdy2_r hdy4_r
    rw [hm_xy_eq]
    linarith
