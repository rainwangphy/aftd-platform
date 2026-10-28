import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStrongProd
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.SimpleGraphCyclePowerAdjIffOfBandwidthLt

/-!
# cycle_strong_product_not_has_equivalence_cover_three

Topic: combinatorics   Node: 8cd134f9954a

Provenance: original. Related work: OP-597

For every m ≥ 6 and n ≥ 5, the strong product of cycles C_m and C_n (simple_graph_strong_prod of simple_graph_cycle_power m 1 and simple_graph_cycle_power n 1) cannot be covered by 3 equivalence subgraphs.
-/

lemma cycle_strong_product_not_has_equivalence_cover_three_cycle_props (k : ℕ) (hk : 5 ≤ k) :
    (simple_graph_cycle_power k 1).Adj (0 : ZMod k) 1 ∧
    (simple_graph_cycle_power k 1).Adj (0 : ZMod k) (-1) ∧
    (1 : ZMod k) ≠ -1 ∧
    ¬ (simple_graph_cycle_power k 1).Adj (1 : ZMod k) (-1) := by
  have : NeZero k := ⟨by omega⟩
  have hadj01 : (simple_graph_cycle_power k 1).Adj 0 1 := by
    rw [simple_graph_cycle_power_adj_iff_of_bandwidth_lt k 1 (by omega)]
    exact ⟨1, by decide, by decide, by ring⟩
  have hadj0neg1 : (simple_graph_cycle_power k 1).Adj 0 (-1) := by
    rw [simple_graph_cycle_power_adj_iff_of_bandwidth_lt k 1 (by omega)]
    exact ⟨-1, by decide, by decide, by ring⟩
  have hne : (1 : ZMod k) ≠ -1 := by
    intro h
    have h2 : ((2 : ℤ) : ZMod k) = ((0 : ℤ) : ZMod k) := by
      push_cast; linear_combination h
    have h_bound : |(2 : ℤ) - 0| < (k : ℤ) := by
      rw [sub_zero, abs_lt]; omega
    have h_eq : (2 : ℤ) = 0 := by
      rwa [zmod_intCast_eq_intCast_iff_of_abs_sub_lt k 2 0 h_bound] at h2
    omega
  have hnot : ¬ (simple_graph_cycle_power k 1).Adj (1 : ZMod k) (-1) := by
    rw [simple_graph_cycle_power_adj_iff_of_bandwidth_lt k 1 (by omega)]
    rintro ⟨e, -, he1, he⟩
    have h2 : ((e + 2 : ℤ) : ZMod k) = ((0 : ℤ) : ZMod k) := by
      push_cast; linear_combination -he
    rw [abs_le] at he1
    have h_bound : |(e + 2) - 0| < (k : ℤ) := by
      rw [sub_zero, abs_lt]; omega
    have h_eq : (e + 2 : ℤ) = 0 := by
      rwa [zmod_intCast_eq_intCast_iff_of_abs_sub_lt k (e + 2) 0 h_bound] at h2
    omega
  exact ⟨hadj01, hadj0neg1, hne, hnot⟩

/-- For m ≥ 6 and n ≥ 5, the strong product C_m ⊠ C_n cannot be covered by 3 equivalence subgraphs. -/
theorem cycle_strong_product_not_has_equivalence_cover_three
    (m n : ℕ) (hm : 6 ≤ m) (hn : 5 ≤ n) :
    ¬ simple_graph_has_equivalence_cover
        (simple_graph_strong_prod (simple_graph_cycle_power m 1) (simple_graph_cycle_power n 1)) 3 := by
  have hm5 : 5 ≤ m := by omega
  rcases cycle_strong_product_not_has_equivalence_cover_three_cycle_props m hm5 with
    ⟨hadj01_m, hadj0neg1_m, hne_m, hnot_m⟩
  rcases cycle_strong_product_not_has_equivalence_cover_three_cycle_props n hn with
    ⟨hadj01_n, hadj0neg1_n, hne_n, hnot_n⟩
  set Gm := simple_graph_cycle_power m 1
  set Gn := simple_graph_cycle_power n 1
  set G := simple_graph_strong_prod Gm Gn
  rintro ⟨c, hc_clique, hc_cov⟩
  let v0 : ZMod m × ZMod n := (0, 0)
  let v1 : ZMod m × ZMod n := (1, 1)
  let v2 : ZMod m × ZMod n := (1, -1)
  let v3 : ZMod m × ZMod n := (-1, 1)
  let v4 : ZMod m × ZMod n := (-1, -1)
  have hadj_v0_v1 : G.Adj v0 v1 :=
    ⟨fun h => hadj01_m.ne (congr_arg Prod.fst h), Or.inr hadj01_m, Or.inr hadj01_n⟩
  have hadj_v0_v2 : G.Adj v0 v2 :=
    ⟨fun h => hadj01_m.ne (congr_arg Prod.fst h), Or.inr hadj01_m, Or.inr hadj0neg1_n⟩
  have hadj_v0_v3 : G.Adj v0 v3 :=
    ⟨fun h => hadj0neg1_m.ne (congr_arg Prod.fst h), Or.inr hadj0neg1_m, Or.inr hadj01_n⟩
  have hadj_v0_v4 : G.Adj v0 v4 :=
    ⟨fun h => hadj0neg1_m.ne (congr_arg Prod.fst h), Or.inr hadj0neg1_m, Or.inr hadj0neg1_n⟩
  rcases hc_cov v0 v1 hadj_v0_v1 with ⟨s1, hs1⟩
  rcases hc_cov v0 v2 hadj_v0_v2 with ⟨s2, hs2⟩
  rcases hc_cov v0 v3 hadj_v0_v3 with ⟨s3, hs3⟩
  rcases hc_cov v0 v4 hadj_v0_v4 with ⟨s4, hs4⟩
  have h_not_adj_m : ¬ (1 : ZMod m) = -1 ∧ ¬ Gm.Adj 1 (-1) := ⟨hne_m, hnot_m⟩
  have h_not_adj_n : ¬ (1 : ZMod n) = -1 ∧ ¬ Gn.Adj 1 (-1) := ⟨hne_n, hnot_n⟩
  have h_not_G_12 : ¬ G.Adj v1 v2 := by
    rintro ⟨-, -, h2⟩
    cases h2 with
    | inl h => exact h_not_adj_n.1 h
    | inr h => exact h_not_adj_n.2 h
  have h_not_G_13 : ¬ G.Adj v1 v3 := by
    rintro ⟨-, h1, -⟩
    cases h1 with
    | inl h => exact h_not_adj_m.1 h
    | inr h => exact h_not_adj_m.2 h
  have h_not_G_14 : ¬ G.Adj v1 v4 := by
    rintro ⟨-, h1, -⟩
    cases h1 with
    | inl h => exact h_not_adj_m.1 h
    | inr h => exact h_not_adj_m.2 h
  have h_not_G_23 : ¬ G.Adj v2 v3 := by
    rintro ⟨-, h1, -⟩
    cases h1 with
    | inl h => exact h_not_adj_m.1 h
    | inr h => exact h_not_adj_m.2 h
  have h_not_G_24 : ¬ G.Adj v2 v4 := by
    rintro ⟨-, h1, -⟩
    cases h1 with
    | inl h => exact h_not_adj_m.1 h
    | inr h => exact h_not_adj_m.2 h
  have h_not_G_34 : ¬ G.Adj v3 v4 := by
    rintro ⟨-, -, h2⟩
    cases h2 with
    | inl h => exact h_not_adj_n.1 h
    | inr h => exact h_not_adj_n.2 h
  have hne_12 : v1 ≠ v2 := fun h => hne_n (congr_arg Prod.snd h)
  have hne_13 : v1 ≠ v3 := fun h => hne_m (congr_arg Prod.fst h)
  have hne_14 : v1 ≠ v4 := fun h => hne_m (congr_arg Prod.fst h)
  have hne_23 : v2 ≠ v3 := fun h => hne_m (congr_arg Prod.fst h)
  have hne_24 : v2 ≠ v4 := fun h => hne_m (congr_arg Prod.fst h)
  have hne_34 : v3 ≠ v4 := fun h => hne_n (congr_arg Prod.snd h)
  have hs12 : s1 ≠ s2 := by
    intro heq
    have h_c : c s1 v1 = c s1 v2 := by rw [← hs1, heq, hs2]
    exact h_not_G_12 (hc_clique s1 v1 v2 hne_12 h_c)
  have hs13 : s1 ≠ s3 := by
    intro heq
    have h_c : c s1 v1 = c s1 v3 := by rw [← hs1, heq, hs3]
    exact h_not_G_13 (hc_clique s1 v1 v3 hne_13 h_c)
  have hs14 : s1 ≠ s4 := by
    intro heq
    have h_c : c s1 v1 = c s1 v4 := by rw [← hs1, heq, hs4]
    exact h_not_G_14 (hc_clique s1 v1 v4 hne_14 h_c)
  have hs23 : s2 ≠ s3 := by
    intro heq
    have h_c : c s2 v2 = c s2 v3 := by rw [← hs2, heq, hs3]
    exact h_not_G_23 (hc_clique s2 v2 v3 hne_23 h_c)
  have hs24 : s2 ≠ s4 := by
    intro heq
    have h_c : c s2 v2 = c s2 v4 := by rw [← hs2, heq, hs4]
    exact h_not_G_24 (hc_clique s2 v2 v4 hne_24 h_c)
  have hs34 : s3 ≠ s4 := by
    intro heq
    have h_c : c s3 v3 = c s3 v4 := by rw [← hs3, heq, hs4]
    exact h_not_G_34 (hc_clique s3 v3 v4 hne_34 h_c)
  have : s1.1 ≠ s2.1 := fun h => hs12 (Fin.ext h)
  have : s1.1 ≠ s3.1 := fun h => hs13 (Fin.ext h)
  have : s1.1 ≠ s4.1 := fun h => hs14 (Fin.ext h)
  have : s2.1 ≠ s3.1 := fun h => hs23 (Fin.ext h)
  have : s2.1 ≠ s4.1 := fun h => hs24 (Fin.ext h)
  have : s3.1 ≠ s4.1 := fun h => hs34 (Fin.ext h)
  have := s1.isLt
  have := s2.isLt
  have := s3.isLt
  have := s4.isLt
  omega
