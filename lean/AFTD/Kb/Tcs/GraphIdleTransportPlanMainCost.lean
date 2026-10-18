import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIdleTransportPlanMain
import AFTD.Kb.Tcs.GraphDistLeTwoOfEdiamLeTwo
import AFTD.Kb.Tcs.GraphEdgePartitionCard

/-!
# graph_idle_transport_plan_main_cost

Topic: graphs   Node: 8dc935a021a6

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

For an edge xy in a graph of diameter at most 2, the main plan from μ_x^{1/2} to μ_y^{1/2} costs at most 1/2 − (1/2)/d_x + 2|B|·(1/2)/d_y.
-/

/-- Cost of the main plan: at most 1/2 − (1/2)/d_x + 2|B|·(1/2)/d_y. -/
theorem graph_idle_transport_plan_main_cost {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : G.Adj x y)
    (hdiam : G.ediam ≤ 2) (A B C P : Finset V)
    (hAmem : ∀ v, v ∈ A ↔ (G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y))
    (hBmem : ∀ v, v ∈ B ↔ (G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x))
    (hCmem : ∀ v, v ∈ C ↔ (G.Adj x v ∧ G.Adj y v))
    (hPmem : ∀ v, v ∈ P ↔ (¬ G.Adj x v ∧ ¬ G.Adj y v))
    (hcover : (Finset.univ : Finset V) = {x} ∪ {y} ∪ A ∪ B ∪ C ∪ P)
    (hdx : G.degree x = A.card + C.card + 1)
    (hdy : G.degree y = B.card + C.card + 1)
    (hle : G.degree x ≤ G.degree y) :
    (∑ u, ∑ v, (G.dist u v : ℝ) * graph_idle_transport_plan_main G x y A B C u v) ≤
      1/2 - (1/2)/(G.degree x : ℝ) + 2*((B.card : ℝ))*((1/2)/(G.degree y : ℝ)) := by
  have open_finset : True := trivial
  let F : V → ℝ := fun u =>
    if u = x ∨ u ∈ C then 1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ)
    else if u ∈ A then 1 / 2 / (G.degree x : ℝ) else 0

  have hdist2 (u v : V) : (G.dist u v : ℝ) ≤ 2 := by
    exact_mod_cast graph_dist_le_two_of_ediam_le_two G hdiam u v
  have hpos_dx : 0 < G.degree x := by
    have : y ∈ G.neighborFinset x := by simp [SimpleGraph.mem_neighborFinset, hxy]
    exact Finset.card_pos.mpr ⟨y, this⟩
  have hpos_dx_R : 0 < (G.degree x : ℝ) := Nat.cast_pos.mpr hpos_dx
  have hle_R : (G.degree x : ℝ) ≤ (G.degree y : ℝ) := Nat.cast_le.mpr hle
  have hpos_dy_R : 0 < (G.degree y : ℝ) := hpos_dx_R.trans_le hle_R
  have hsub_nonneg : 0 ≤ 1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ) := by
    rw [sub_nonneg]
    exact div_le_div_of_nonneg_left (by norm_num) hpos_dx_R hle_R

  have hle_pointwise (u v : V) :
      (G.dist u v : ℝ) * graph_idle_transport_plan_main G x y A B C u v ≤
        (if u = x ∧ v = y then 1 / 2 - 1 / 2 / (G.degree x : ℝ) else 0) +
        2 * (if v ∈ B then F u / (B.card : ℝ) else 0) := by
    have hpos_p4 : 0 ≤ if v ∈ B then F u / (B.card : ℝ) else 0 := by
      dsimp [F]
      split_ifs with hv hu1 hu2
      · exact div_nonneg hsub_nonneg (Nat.cast_nonneg _)
      · exact div_nonneg (div_nonneg (by norm_num) (by linarith)) (Nat.cast_nonneg _)
      · simp
      · simp
    have hd4 : (G.dist u v : ℝ) * (if v ∈ B then F u / (B.card : ℝ) else 0) ≤
        2 * (if v ∈ B then F u / (B.card : ℝ) else 0) :=
      mul_le_mul_of_nonneg_right (hdist2 u v) hpos_p4
    unfold graph_idle_transport_plan_main
    have hd1 : (G.dist u v : ℝ) * (if u = x ∧ v = x then 1 / 2 / (G.degree y : ℝ) else 0) = 0 := by
      split_ifs with h
      · rcases h with ⟨rfl, rfl⟩; simp
      · ring
    have hd2 : (G.dist u v : ℝ) * (if v = y then if u = x then 1 / 2 - 1 / 2 / (G.degree x : ℝ) else if u = y then 1 / 2 / (G.degree x : ℝ) else 0 else 0) =
        if u = x ∧ v = y then 1 / 2 - 1 / 2 / (G.degree x : ℝ) else 0 := by
      by_cases hv : v = y
      · subst v
        by_cases hu : u = x
        · subst u
          have : (G.dist x y : ℝ) = 1 := by simp [SimpleGraph.dist_eq_one_iff_adj.mpr hxy]
          simp [this]
        · simp [hu]
          by_cases huy : u = y
          · subst u; simp
          · simp [huy]
      · simp [hv]
    have hd3 : (G.dist u v : ℝ) * (if u = v then if u ∈ C then 1 / 2 / (G.degree y : ℝ) else 0 else 0) = 0 := by
      split_ifs with h1 h2
      · subst h1; simp
      · ring
      · ring
    change (G.dist u v : ℝ) * (((if u = x ∧ v = x then 1 / 2 / (G.degree y : ℝ) else 0) +
        (if v = y then if u = x then 1 / 2 - 1 / 2 / (G.degree x : ℝ) else if u = y then 1 / 2 / (G.degree x : ℝ) else 0 else 0) +
        (if u = v then if u ∈ C then 1 / 2 / (G.degree y : ℝ) else 0 else 0)) +
        (if v ∈ B then F u / (B.card : ℝ) else 0)) ≤ _
    linarith

  have hsum_le : (∑ u, ∑ v, (G.dist u v : ℝ) * graph_idle_transport_plan_main G x y A B C u v) ≤
      ∑ u, ∑ v, ((if u = x ∧ v = y then 1 / 2 - 1 / 2 / (G.degree x : ℝ) else 0) +
        2 * (if v ∈ B then F u / (B.card : ℝ) else 0)) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hle_pointwise u v

  apply hsum_le.trans
  have hx_not_C : x ∉ C := by
    intro hc
    have h := (hCmem x).mp hc
    exact G.irrefl h.1
  have hx_not_A : x ∉ A := by
    intro ha
    have h := (hAmem x).mp ha
    exact G.irrefl h.1
  have hdisj_AC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro v hvA hvC
    have h1 := ((hAmem v).mp hvA).2.1
    have h2 := ((hCmem v).mp hvC).2
    exact h1 h2

  have hF (u : V) : F u =
      (if u = x then 1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ) else 0) +
      (if u ∈ C then 1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ) else 0) +
      (if u ∈ A then 1 / 2 / (G.degree x : ℝ) else 0) := by
    dsimp [F]
    by_cases hux : u = x
    · subst u
      simp [hx_not_C, hx_not_A]
    · simp [hux]
      by_cases huC : u ∈ C
      · have : u ∉ A := fun huA => (Finset.disjoint_left.mp hdisj_AC huA) huC
        simp [huC, this]
      · simp [huC]

  have hsum_F : (∑ u, F u) = (B.card : ℝ) * (1 / 2 / (G.degree y : ℝ)) := by
    simp_rw [hF]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : (∑ u, if u = x then 1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ) else 0) =
        1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ) := by simp
    have h2 : (∑ u, if u ∈ C then 1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ) else 0) =
        (C.card : ℝ) * (1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ)) := by
      have : (∑ u, if u ∈ C then 1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ) else 0) =
          ∑ u ∈ C, (1 / 2 / (G.degree x : ℝ) - 1 / 2 / (G.degree y : ℝ)) := by
        rw [← Finset.sum_filter]; congr 1; ext v; simp
      rw [this]
      simp only [Finset.sum_const, nsmul_eq_mul]
    have h3 : (∑ u, if u ∈ A then 1 / 2 / (G.degree x : ℝ) else 0) =
        (A.card : ℝ) * (1 / 2 / (G.degree x : ℝ)) := by
      have : (∑ u, if u ∈ A then 1 / 2 / (G.degree x : ℝ) else 0) =
          ∑ u ∈ A, (1 / 2 / (G.degree x : ℝ)) := by
        rw [← Finset.sum_filter]; congr 1; ext v; simp
      rw [this]
      simp only [Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2, h3]
    have hdx_R : (G.degree x : ℝ) = (A.card : ℝ) + (C.card : ℝ) + 1 := by
      exact_mod_cast hdx
    have hdy_R : (G.degree y : ℝ) = (B.card : ℝ) + (C.card : ℝ) + 1 := by
      exact_mod_cast hdy
    have hd1 : 1 / 2 / (G.degree x : ℝ) = 1 / (2 * (G.degree x : ℝ)) := by ring
    have hd2 : 1 / 2 / (G.degree y : ℝ) = 1 / (2 * (G.degree y : ℝ)) := by ring
    rw [hd1, hd2]
    field_simp
    rw [hdx_R, hdy_R]
    ring

  simp_rw [Finset.sum_add_distrib]
  have hsum_xy : (∑ u, ∑ v, if u = x ∧ v = y then 1 / 2 - 1 / 2 / (G.degree x : ℝ) else 0) =
      1 / 2 - 1 / 2 / (G.degree x : ℝ) := by
    have h (u v : V) : (if u = x ∧ v = y then 1 / 2 - 1 / 2 / (G.degree x : ℝ) else (0 : ℝ)) =
        (if u = x then if v = y then 1 / 2 - 1 / 2 / (G.degree x : ℝ) else 0 else 0) := by
      split_ifs <;> tauto
    simp_rw [h]
    simp
  rw [hsum_xy]
  simp_rw [← Finset.mul_sum]
  have hsum_v (u : V) : (∑ v, if v ∈ B then F u / (B.card : ℝ) else (0 : ℝ)) =
      if B = ∅ then 0 else F u := by
    by_cases hB : B = ∅
    · simp [hB]
    · have hB_card : (B.card : ℝ) ≠ 0 := by
        have : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
        have : 0 < B.card := Finset.Nonempty.card_pos this
        positivity
      have hsum : (∑ v, if v ∈ B then F u / (B.card : ℝ) else 0) = ∑ v ∈ B, (F u / (B.card : ℝ)) := by
        rw [← Finset.sum_filter]; congr 1; ext v; simp
      rw [hsum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hB_card]
      simp [hB]
  simp_rw [hsum_v]
  have hB_sum : (∑ x, if B = ∅ then 0 else F x) = (B.card : ℝ) * (1 / 2 / (G.degree y : ℝ)) := by
    by_cases hB : B = ∅
    · subst hB; simp
    · simp [hB, hsum_F]
  rw [hB_sum]
  ring_nf
  rfl
