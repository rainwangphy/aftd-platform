import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCardCommonNeighborsAddTwoLeDegree
import AFTD.Kb.Tcs.IsAmplyRegular

/-!
# amply_regular_diameter_bound_of_diam_le_two

Topic: graphs   Node: fc0c61a59f75

Provenance: helper lemma. step towards amply_regular_diameter_bound_conjecture

An amply regular graph with parameters (k, ℓ, μ) whose diameter is at most 2 has diameter at most 2k/(ℓ+2). No hypothesis on μ is needed: for diameter 1 one has ℓ < k, and for diameter 2 one has ℓ + 2 ≤ k.
-/

/-- Easy half of Conjecture 3.7: if the diameter is at most 2 the bound holds for every amply regular graph, with no hypothesis on μ (so in particular for μ > 2). -/
theorem amply_regular_diameter_bound_of_diam_le_two {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k ℓ μ : ℕ} (hG : IsAmplyRegular G k ℓ μ) (h2 : G.diam ≤ 2) :
    G.diam ≤ 2 * k / (ℓ + 2) := by
  classical
  rcases Nat.lt_or_ge G.diam 1 with h1 | h1
  · have hd0 : G.diam = 0 := by omega
    rw [hd0]; exact Nat.zero_le _
  rcases Nat.lt_or_ge G.diam 2 with h2' | h2''
  · have hd1 : G.diam = 1 := by omega
    have : Nonempty V :=
      (SimpleGraph.nontrivial_of_diam_ne_zero (by rw [hd1]; norm_num)).to_nonempty
    obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
    have hnt : G.edist u v ≠ ⊤ := by
      intro htop; rw [SimpleGraph.dist, htop, ENat.toNat_top] at huv; omega
    have h1' : (G.edist u v).toNat = 1 := huv.trans hd1
    have hed : G.edist u v = 1 := by rw [← ENat.natCast_toNat hnt, h1']; rfl
    have hadj : G.Adj u v := SimpleGraph.edist_eq_one_iff_adj.mp hed
    have hlt : ℓ < k := by
      have hh := SimpleGraph.Adj.card_commonNeighbors_lt_degree hadj
      rw [hG.adj_commonNeighbors hadj, hG.regular u] at hh; exact hh
    rw [hd1, Nat.le_div_iff_mul_le (k := ℓ + 2) (by omega)]
    omega
  · have hd2 : G.diam = 2 := by omega
    have : Nonempty V :=
      (SimpleGraph.nontrivial_of_diam_ne_zero (by rw [hd2]; norm_num)).to_nonempty
    obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
    have hnt : G.edist u v ≠ ⊤ := by
      intro htop; rw [SimpleGraph.dist, htop, ENat.toNat_top] at huv; omega
    have h1' : (G.edist u v).toNat = 2 := huv.trans hd2
    have hed : G.edist u v = 2 := by rw [← ENat.natCast_toNat hnt, h1']; rfl
    obtain ⟨hne', hnadj, hcommon⟩ := SimpleGraph.edist_eq_two_iff.mp hed
    obtain ⟨w, hw⟩ := hcommon
    rw [SimpleGraph.mem_commonNeighbors] at hw
    have hcount : Fintype.card (G.commonNeighbors u w) + 2 ≤ k :=
      simple_graph_card_commonNeighbors_add_two_le_degree G hG.regular hne' hw.1 hw.2 hnadj
    have hEll : Fintype.card (G.commonNeighbors u w) = ℓ := hG.adj_commonNeighbors hw.1
    rw [hd2, Nat.le_div_iff_mul_le (k := ℓ + 2) (by omega)]
    omega
