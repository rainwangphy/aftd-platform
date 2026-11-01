import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphExistsGeodesicVertexFamily

/-!
# simple_graph_diam_le_two_mul_div_add_one_of_dist_two_transport_bound_of_le

Topic: graphs   Node: 32dad34c3ad0

Provenance: helper lemma. step towards simple_graph_diam_le_two_mul_div_add_one_of_dist_two_transport_bound

Discrete Bonnet–Myers: if every vertex of a finite graph G has degree k, c ≤ k, and every pair at distance 2 satisfies the one-sided 1-Lipschitz sum bound with parameter c > 0, i.e. Σ_{N(q)} f − Σ_{N(p)} f ≤ 2(k − c) for every 1-Lipschitz f, then diam G ≤ 2k/c + 1.
-/

/-- Discrete Bonnet–Myers: if every vertex of a finite graph G has degree k, c ≤ k, and every pair at distance 2 satisfies the one-sided 1-Lipschitz sum bound with parameter c > 0, then diam G ≤ 2k/c + 1. -/
theorem simple_graph_diam_le_two_mul_div_add_one_of_dist_two_transport_bound_of_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k c : ℕ} (hreg : G.IsRegularOfDegree k) (hc : 0 < c)
    (hck : c ≤ k)
    (hbound : ∀ (p q : V), G.dist p q = 2 → ∀ f : V → ℝ,
      (∀ a b : V, |f a - f b| ≤ (G.dist a b : ℝ)) →
      ∑ z ∈ G.neighborFinset q, f z - ∑ z ∈ G.neighborFinset p, f z ≤ 2 * ((k - c : ℕ) : ℝ)) :
    G.diam ≤ 2 * k / c + 1 := by
  by_cases hd : G.diam ≤ 1
  · have : 0 ≤ 2 * k / c := Nat.zero_le _
    omega
  · push Not at hd
    have hne : Nonempty V := by
      by_contra he
      have : IsEmpty V := not_nonempty_iff.mp he
      have hd0 : G.diam = 0 := SimpleGraph.diam_eq_zero.mpr (Or.inr inferInstance)
      omega
    have he : G.ediam ≠ ⊤ := by
      intro htop
      have : G.diam = 0 := by rw [SimpleGraph.diam, htop]; rfl
      omega
    have hconn : G.Connected := G.connected_of_ediam_ne_top he
    obtain ⟨x, y, hxy⟩ := SimpleGraph.exists_dist_eq_diam (G := G)
    have hr : G.Reachable x y := hconn x y
    obtain ⟨v, hv0, hvd, hdist⟩ := simple_graph_exists_geodesic_vertex_family G hxy hr
    let f (w : V) : ℝ := (G.dist x w : ℝ)
    have hf_lip : ∀ a b : V, |f a - f b| ≤ (G.dist a b : ℝ) := by
      intro a b
      rw [abs_le]
      constructor
      · have h1 : (G.dist x b : ℝ) ≤ (G.dist x a : ℝ) + (G.dist a b : ℝ) := by
          exact_mod_cast hconn.dist_triangle (u := x) (v := a) (w := b)
        linarith
      · have h2 : (G.dist x a : ℝ) ≤ (G.dist x b : ℝ) + (G.dist b a : ℝ) := by
          exact_mod_cast hconn.dist_triangle (u := x) (v := b) (w := a)
        rw [SimpleGraph.dist_comm (u := b) (v := a)] at h2
        linarith
    have hdeg : ∀ w : V, (G.neighborFinset w).card = k := by
      intro w
      rw [SimpleGraph.card_neighborFinset_eq_degree, hreg w]
    let F (w : V) : ℝ := ∑ z ∈ G.neighborFinset w, f z - (k : ℝ) * f w
    let m := G.diam / 2
    have hstep : ∀ j ∈ Finset.range m, 2 * (c : ℝ) ≤ F (v (2 * j)) - F (v (2 * (j + 1))) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj1 : 2 * j ≤ G.diam := by omega
      have hj2 : 2 * (j + 1) ≤ G.diam := by omega
      have hpq_dist : G.dist (v (2 * j)) (v (2 * (j + 1))) = 2 := by
        rw [hdist (2 * j) (2 * (j + 1)) hj1 hj2]
        rw [Nat.dist_eq_sub_of_le (by omega)]
        omega
      have hb := hbound (v (2 * j)) (v (2 * (j + 1))) hpq_dist f hf_lip
      rw [Nat.cast_sub hck] at hb
      have hf_p : f (v (2 * j)) = 2 * (j : ℝ) := by
        dsimp [f]
        rw [← hv0, hdist 0 (2 * j) (by omega) hj1, Nat.dist_zero_left]
        push_cast; ring
      have hf_q : f (v (2 * (j + 1))) = 2 * ((j : ℝ) + 1) := by
        dsimp [f]
        rw [← hv0, hdist 0 (2 * (j + 1)) (by omega) hj2, Nat.dist_zero_left]
        push_cast; ring
      have hdiff : (k : ℝ) * f (v (2 * (j + 1))) - (k : ℝ) * f (v (2 * j)) = 2 * (k : ℝ) := by
        rw [hf_p, hf_q]
        ring
      dsimp [F]
      linarith
    have htele : ∑ j ∈ Finset.range m, (F (v (2 * j)) - F (v (2 * (j + 1)))) =
        F (v 0) - F (v (2 * m)) := by
      exact Finset.sum_range_sub' (fun j => F (v (2 * j))) m
    have hsum_le : (m : ℝ) * (2 * (c : ℝ)) ≤ F (v 0) - F (v (2 * m)) := by
      calc (m : ℝ) * (2 * (c : ℝ)) = ∑ j ∈ Finset.range m, (2 * (c : ℝ)) := by
             rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
           _ ≤ ∑ j ∈ Finset.range m, (F (v (2 * j)) - F (v (2 * (j + 1)))) :=
             Finset.sum_le_sum hstep
           _ = F (v 0) - F (v (2 * m)) := htele
    have hfx : f (v 0) = 0 := by
      dsimp [f]
      rw [hv0, SimpleGraph.dist_self, Nat.cast_zero]
    have hFx : F (v 0) = k := by
      dsimp [F]
      have hfn : ∀ z ∈ G.neighborFinset (v 0), f z = 1 := by
        intro z hz
        dsimp [f]
        rw [hv0] at hz
        rw [SimpleGraph.mem_neighborFinset] at hz
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hz, Nat.cast_one]
      have hsum1 : (∑ z ∈ G.neighborFinset (v 0), f z) = k := by
        rw [Finset.sum_congr rfl hfn, Finset.sum_const, nsmul_eq_mul, mul_one, hdeg]
      rw [hfx, mul_zero, sub_zero, hsum1]
    have hFw : -(k : ℝ) ≤ F (v (2 * m)) := by
      dsimp [F]
      have hrew : (k : ℝ) * f (v (2 * m)) = ∑ z ∈ G.neighborFinset (v (2 * m)), f (v (2 * m)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hdeg]
      rw [hrew, ← Finset.sum_sub_distrib]
      have hlip : ∀ z ∈ G.neighborFinset (v (2 * m)), (-1 : ℝ) ≤ f z - f (v (2 * m)) := by
        intro z hz
        have hlip' := hf_lip z (v (2 * m))
        rw [abs_le] at hlip'
        have hadj : G.Adj (v (2 * m)) z := by
          rw [SimpleGraph.mem_neighborFinset] at hz
          exact hz
        have hdz : G.dist z (v (2 * m)) = 1 := by
          rw [SimpleGraph.dist_comm]
          exact SimpleGraph.dist_eq_one_iff_adj.mpr hadj
        rw [hdz, Nat.cast_one] at hlip'
        linarith
      have hle : (∑ z ∈ G.neighborFinset (v (2 * m)), (-1 : ℝ)) ≤
          ∑ z ∈ G.neighborFinset (v (2 * m)), (f z - f (v (2 * m))) :=
        Finset.sum_le_sum hlip
      rw [Finset.sum_const, nsmul_eq_mul, hdeg] at hle
      linarith
    have hbound2k : F (v 0) - F (v (2 * m)) ≤ 2 * (k : ℝ) := by
      linarith [hFx, hFw]
    have h2mc : (2 * m * c : ℝ) ≤ 2 * (k : ℝ) := by
      calc (2 * m * c : ℝ) = (m : ℝ) * (2 * (c : ℝ)) := by ring
        _ ≤ F (v 0) - F (v (2 * m)) := hsum_le
        _ ≤ 2 * (k : ℝ) := hbound2k
    have h2mc_nat : 2 * m * c ≤ 2 * k := by
      exact_mod_cast h2mc
    have hdiv : 2 * m ≤ 2 * k / c := by
      rw [Nat.le_div_iff_mul_le hc]
      omega
    have hdiam_le : G.diam ≤ 2 * m + 1 := by
      dsimp [m]
      omega
    omega
