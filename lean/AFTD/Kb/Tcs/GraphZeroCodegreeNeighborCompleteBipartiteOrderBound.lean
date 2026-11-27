import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# graph_zero_codegree_neighbor_complete_bipartite_order_bound

Topic: graphs   Node: 192388f0d93d

Provenance: helper lemma. OP-1957: parameterized refinement of the root-layer degree count.

For r between two and d, if a graph of maximum degree at most d has a complete bipartite r-by-r graph between the endpoint neighborhoods of every nonadjacent pair with no common neighbor, then r² times its order is bounded by r²(1+d²)+d(d−1) max(d−r²,0).
-/

theorem gzc_double_count {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (X Y : Finset (Fin n)) :
    ∑ x ∈ X, (Y.filter (H.Adj x)).card = ∑ y ∈ Y, (X.filter (H.Adj y)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  simp [H.adj_comm]

theorem gzc_two_parts {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (x : Fin n) (Y Z : Finset (Fin n)) (hYZ : Disjoint Y Z) :
    (Y.filter (H.Adj x)).card + (Z.filter (H.Adj x)).card ≤ H.degree x := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hYZ),
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_union, Finset.mem_filter] at hy
  rw [SimpleGraph.mem_neighborFinset]
  rcases hy with h | h <;> exact h.2

theorem graph_zero_codegree_neighbor_complete_bipartite_order_bound
    (n d r : ℕ) (hr : 2 ≤ r) (hrd : r ≤ d) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hmax : ∀ u, H.degree u ≤ d)
    (hcomplete : ∀ u v, u ≠ v → ¬ H.Adj u v → (∀ x, ¬ (H.Adj u x ∧ H.Adj v x)) →
      ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧
        (∀ a ∈ A, H.Adj u a) ∧ (∀ b ∈ B, H.Adj v b) ∧
        ∀ a ∈ A, ∀ b ∈ B, H.Adj a b) :
    r*r*n ≤ r*r*(1+d*d) + d*(d-1)*(d-r*r) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  let u : Fin n := ⟨0, hn⟩
  let N := H.neighborFinset u
  let S2 := Finset.univ.filter fun v => v ≠ u ∧ ¬ H.Adj u v ∧ ∃ x, H.Adj u x ∧ H.Adj v x
  let S3 := Finset.univ.filter fun v => v ≠ u ∧ ¬ H.Adj u v ∧ ∀ x, ¬ (H.Adj u x ∧ H.Adj v x)
  let T := S2.filter fun w => r ≤ (N.filter (H.Adj w)).card
  have hN : N.card ≤ d := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hmax u
  -- partition of the vertex set
  have hpart : n ≤ 1 + N.card + S2.card + S3.card := by
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {u} ∪ N ∪ S2 ∪ S3 := by
      intro v _
      simp only [Finset.mem_union, Finset.mem_singleton, N, S2, S3, Finset.mem_filter,
        Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
      by_cases h1 : v = u
      · left; left; left; exact h1
      by_cases h2 : H.Adj u v
      · left; left; right; exact h2
      by_cases h3 : ∃ x, H.Adj u x ∧ H.Adj v x
      · left; right; exact ⟨h1, h2, h3⟩
      · right; push_neg at h3; exact ⟨h1, h2, fun x hx => h3 x hx.1 hx.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine this.trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    refine Nat.add_le_add_right ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) _)) _
    rw [Finset.card_singleton]
  -- edges between N and S2
  have hNS2_upper : ∑ x ∈ N, (S2.filter (H.Adj x)).card ≤ d * (d - 1) := by
    calc ∑ x ∈ N, (S2.filter (H.Adj x)).card ≤ ∑ _x ∈ N, (d - 1) := by
          apply Finset.sum_le_sum
          intro x hx
          have hux : H.Adj x u := (H.mem_neighborFinset u x).1 hx |>.symm
          have hdisj : Disjoint S2 {u} := by
            rw [Finset.disjoint_singleton_right]
            simp [S2]
          have h := gzc_two_parts H x S2 {u} hdisj
          have hu1 : (({u} : Finset (Fin n)).filter (H.Adj x)).card = 1 := by
            rw [Finset.filter_singleton, if_pos hux, Finset.card_singleton]
          have := hmax x
          omega
      _ = N.card * (d - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ d * (d - 1) := Nat.mul_le_mul_right _ hN
  have hNS2_lower : S2.card + (r - 1) * T.card ≤ ∑ w ∈ S2, (N.filter (H.Adj w)).card := by
    have h1 : ∀ w ∈ S2, 1 + (if w ∈ T then r - 1 else 0) ≤ (N.filter (H.Adj w)).card := by
      intro w hw
      have hw' := hw
      simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and] at hw'
      obtain ⟨x, hux, hwx⟩ := hw'.2.2
      have hpos : 1 ≤ (N.filter (H.Adj w)).card := by
        apply Finset.card_pos.2
        exact ⟨x, Finset.mem_filter.2 ⟨(H.mem_neighborFinset u x).2 hux, hwx⟩⟩
      split_ifs with hT
      · have := (Finset.mem_filter.1 hT).2
        omega
      · omega
    calc S2.card + (r - 1) * T.card
        = ∑ w ∈ S2, (1 + if w ∈ T then r - 1 else 0) := by
          have hfil : S2.filter (fun w => w ∈ T) = T := by
            ext w
            simp only [Finset.mem_filter]
            exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.1 h).1, h⟩⟩
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
            ← Finset.sum_filter, hfil, Finset.sum_const, smul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum h1
  have hS2T : S2.card + (r - 1) * T.card ≤ d * (d - 1) := by
    rw [gzc_double_count H N S2] at hNS2_upper
    exact hNS2_lower.trans hNS2_upper
  -- edges between T and S3
  have hTS3_upper : ∑ t ∈ T, (S3.filter (H.Adj t)).card ≤ T.card * (d - r) := by
    calc ∑ t ∈ T, (S3.filter (H.Adj t)).card ≤ ∑ _t ∈ T, (d - r) := by
          apply Finset.sum_le_sum
          intro t ht
          have hdisj : Disjoint S3 N := by
            rw [Finset.disjoint_left]
            intro v hv hvN
            simp only [S3, Finset.mem_filter, Finset.mem_univ, true_and] at hv
            exact hv.2.1 ((H.mem_neighborFinset u v).1 hvN)
          have h := gzc_two_parts H t S3 N hdisj
          have hr' := (Finset.mem_filter.1 ht).2
          have := hmax t
          omega
      _ = T.card * (d - r) := by rw [Finset.sum_const, smul_eq_mul]
  have hTS3_lower : r * S3.card ≤ ∑ v ∈ S3, (T.filter (H.Adj v)).card := by
    calc r * S3.card = ∑ _v ∈ S3, r := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        have hv' := hv
        simp only [S3, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
        obtain ⟨A, B, hA, hB, hAu, hBv, hAB⟩ := hcomplete u v hv'.1.symm hv'.2.1 hv'.2.2
        rw [← hB]
        apply Finset.card_le_card
        intro b hb
        rw [Finset.mem_filter]
        refine ⟨?_, hBv b hb⟩
        have hbu : b ≠ u := by
          rintro rfl; exact hv'.2.1 (hBv u hb).symm
        have hbN : ¬ H.Adj u b := fun h => hv'.2.2 b ⟨h, hBv b hb⟩
        have hAne : A.Nonempty := by rw [← Finset.card_pos, hA]; omega
        obtain ⟨a, ha⟩ := hAne
        have hbS2 : b ∈ S2 := by
          simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hbu, hbN, a, hAu a ha, (hAB a ha b hb).symm⟩
        refine Finset.mem_filter.2 ⟨hbS2, ?_⟩
        rw [← hA]
        apply Finset.card_le_card
        intro a' ha'
        exact Finset.mem_filter.2 ⟨(H.mem_neighborFinset u a').2 (hAu a' ha'), (hAB a' ha' b hb).symm⟩
  have hS3T : r * S3.card ≤ T.card * (d - r) := by
    rw [gzc_double_count H S3 T] at hTS3_lower
    exact hTS3_lower.trans hTS3_upper
  -- arithmetic
  have hTS2 : T.card ≤ S2.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hrT : r * T.card ≤ d * (d - 1) := by
    have hr1 : r = (r - 1) + 1 := by omega
    have : r * T.card = T.card + (r - 1) * T.card := by
      nth_rewrite 1 [hr1]; ring
    omega
  -- r*n ≤ r*(1+d) + r*S2 + r*S3
  have hrn : r * n ≤ r * (1 + d) + r * S2.card + r * S3.card := by
    have := Nat.mul_le_mul_left r hpart
    have h2 := Nat.mul_le_mul_left r hN
    nlinarith
  have hrS2 : r * S2.card + r * (r - 1) * T.card ≤ r * (d * (d - 1)) := by
    have := Nat.mul_le_mul_left r hS2T
    nlinarith
  -- work over ℤ
  have hd1 : 1 ≤ d := by omega
  zify [hd1, show 1 ≤ r by omega] at hrn hrS2 hS3T hrT ⊢
  have hdr : ((d - r : ℕ) : ℤ) = (d : ℤ) - r := by push_cast [Nat.cast_sub hrd]; ring
  rw [hdr] at hS3T
  rcases le_or_gt (r * r) d with hle | hlt
  · have hcast : ((d - r * r : ℕ) : ℤ) = (d : ℤ) - r * r := by
      push_cast [Nat.cast_sub hle]; ring
    rw [hcast]
    have hT0 : (0 : ℤ) ≤ T.card := by positivity
    have hS30 : (0 : ℤ) ≤ S3.card := by positivity
    have hr0 : (0 : ℤ) ≤ r := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hrT (show (0:ℤ) ≤ (d : ℤ) - r * r by
      have : (r * r : ℤ) ≤ d := by exact_mod_cast hle
      linarith)]
  · have hcast : ((d - r * r : ℕ) : ℤ) = 0 := by
      rw [Nat.sub_eq_zero_of_le hlt.le]; simp
    rw [hcast]
    have hT0 : (0 : ℤ) ≤ T.card := by positivity
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hlt' : (d : ℤ) < r * r := by exact_mod_cast hlt
    nlinarith [mul_le_mul_of_nonneg_left hrn hr0, mul_le_mul_of_nonneg_left hrS2 hr0,
      mul_le_mul_of_nonneg_left hS3T hr0,
      mul_nonneg (mul_nonneg hr0 hT0) (sub_nonneg.2 hlt'.le)]
