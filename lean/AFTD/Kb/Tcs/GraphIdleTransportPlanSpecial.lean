import AFTD.Prelude
import AFTD.Kb.Tcs.GraphDistLeTwoOfEdiamLeTwo
import AFTD.Kb.Tcs.GraphEdgePartitionCard
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_idle_transport_plan_special

Topic: graphs   Node: fb0fad3cbaf8

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

If the edge partition has |A| = |B| ≥ 1, deg x = deg y, |B| = |C|+2 and an A–B edge, then μ_x^{1/2} and μ_y^{1/2} admit a plan of cost at most 1/2 + 2(|A|−1)(1/2)/d_y.
-/

/-- In the boundary configuration there is a transport plan of cost at most 1/2 + 2(|A|-1)·(1/2)/d_y, which is strictly below 1. -/
theorem graph_idle_transport_plan_special {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : G.Adj x y)
    (hdiam : G.ediam ≤ 2) (A B C P : Finset V)
    (hAmem : ∀ v, v ∈ A ↔ (G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y))
    (hBmem : ∀ v, v ∈ B ↔ (G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x))
    (hCmem : ∀ v, v ∈ C ↔ (G.Adj x v ∧ G.Adj y v))
    (hPmem : ∀ v, v ∈ P ↔ (¬ G.Adj x v ∧ ¬ G.Adj y v))
    (hcover : (Finset.univ : Finset V) = {x} ∪ {y} ∪ A ∪ B ∪ C ∪ P)
    (hdx : G.degree x = A.card + C.card + 1)
    (hdy : G.degree y = B.card + C.card + 1)
    (hAB : A.card = B.card) (hne : 1 ≤ A.card)
    (hadj : ∃ v ∈ A, ∃ u ∈ B, G.Adj v u) :
    ∃ π : V → V → ℝ, (∀ u v, 0 ≤ π u v) ∧
      (∀ u, ∑ v, π u v = graph_idle_measure G (1/2) x u) ∧
      (∀ v, ∑ u, π u v = graph_idle_measure G (1/2) y v) ∧
      (∑ u, ∑ v, (G.dist u v : ℝ) * π u v) ≤
        1/2 + 2*((A.card : ℝ) - 1)*((1/2)/(G.degree y : ℝ)) := by
  rcases hadj with ⟨v0, hv0, u0, hu0, hadj0⟩
  let γ := (1/2)/(G.degree y : ℝ)
  let π : V → V → ℝ := fun u v =>
    (if u = x ∧ v = x then γ else 0) +
    (if u = x ∧ v = y then 1/2 - γ else 0) +
    (if u = y ∧ v = y then γ else 0) +
    (if u = v ∧ u ∈ C then γ else 0) +
    (if u = v0 ∧ v = u0 then γ else 0) +
    (if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else 0)
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · intro u v
    have hdypos : (0:ℝ) < (G.degree y : ℝ) := by
      have : 0 < G.degree y := by
        rw [SimpleGraph.degree_pos_iff_exists_adj]; exact ⟨x, hxy.symm⟩
      exact_mod_cast this
    have hγnn : (0:ℝ) ≤ γ := div_nonneg (by norm_num) (by positivity)
    have hγle : γ ≤ 1/2 := by
      dsimp [γ]
      rw [div_le_iff₀ hdypos]
      have h1 : (1:ℝ) ≤ (G.degree y : ℝ) := by
        have : 0 < G.degree y := by
          rw [SimpleGraph.degree_pos_iff_exists_adj]; exact ⟨x, hxy.symm⟩
        exact_mod_cast this
      linarith
    have hAdenom : (0:ℝ) ≤ (A.card : ℝ) - 1 := by
      have : (1:ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hne
      linarith
    dsimp [π]
    repeat' apply add_nonneg
    · split_ifs; exact hγnn; rfl
    · split_ifs; linarith; rfl
    · split_ifs; exact hγnn; rfl
    · split_ifs; exact hγnn; rfl
    · split_ifs; exact hγnn; rfl
    · split_ifs
      · exact div_nonneg hγnn hAdenom
      · rfl
  · intro u
    have hu_cases : ∀ u : V, u = x ∨ u = y ∨ u ∈ A ∨ u ∈ B ∨ u ∈ C ∨ u ∈ P := by
      intro w
      have h : w ∈ (Finset.univ : Finset V) := Finset.mem_univ w
      rw [hcover] at h
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      tauto
    have e1 : (∑ v, if u = x ∧ v = x then γ else (0:ℝ)) = if u = x then γ else 0 := by
      by_cases h : u = x <;> simp [h]
    have e2 : (∑ v, if u = x ∧ v = y then 1/2 - γ else (0:ℝ)) = if u = x then 1/2 - γ else 0 := by
      by_cases h : u = x <;> simp [h]
    have e3 : (∑ v, if u = y ∧ v = y then γ else (0:ℝ)) = if u = y then γ else 0 := by
      by_cases h : u = y <;> simp [h]
    have e4 : (∑ v, if u = v ∧ u ∈ C then γ else (0:ℝ)) = if u ∈ C then γ else 0 := by
      have : (∑ v, if u = v ∧ u ∈ C then γ else (0:ℝ)) = ∑ v, if v = u then (if u ∈ C then γ else 0) else 0 := by
        apply Finset.sum_congr rfl; intro v _; by_cases h : u = v <;> simp [h, eq_comm]
      rw [this]; simp
    have e5 : (∑ v, if u = v0 ∧ v = u0 then γ else (0:ℝ)) = if u = v0 then γ else 0 := by
      by_cases h : u = v0 <;> simp [h]
    have e6 : (∑ v, if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else (0:ℝ)) =
        if u ∈ A \ {v0} then γ else 0 := by
      by_cases hu : u ∈ A \ {v0}
      · simp only [hu, true_and, if_true]
        have huA : u ∈ A := Finset.mem_sdiff.mp hu |>.1
        have hne' : u ≠ v0 := by
          have := Finset.mem_sdiff.mp hu |>.2
          simp only [Finset.mem_singleton] at this
          exact this
        have hA2 : 2 ≤ A.card := by
          have : {u, v0} ⊆ A := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption
          have hle := Finset.card_le_card this
          rw [Finset.card_pair hne'] at hle
          exact hle
        have hdenom : (A.card : ℝ) - 1 ≠ 0 := by
          have : 1 < A.card := hA2
          have : (1 : ℝ) < (A.card : ℝ) := Nat.one_lt_cast.mpr this
          linarith
        have hsum : (∑ v, (if v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else (0 : ℝ))) =
            ∑ v ∈ B \ {u0}, (γ / ((A.card : ℝ) - 1)) := by
          rw [← Finset.sum_filter]; congr 1; ext v; simp
        rw [hsum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sdiff_singleton_eq_erase, Finset.cast_card_erase_of_mem hu0, ← hAB]
        exact mul_div_cancel₀ γ hdenom
      · simp [hu]
    have e56 : (if u = v0 then γ else 0) + (if u ∈ A \ {v0} then γ else 0) =
        if u ∈ A then γ else 0 := by
      by_cases huA : u ∈ A
      · by_cases huv0 : u = v0
        · subst huv0; simp [Finset.mem_sdiff, huA]
        · have : u ∈ A \ {v0} := by
            rw [Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨huA, huv0⟩
          simp [huv0, this, huA]
      · have h1 : u ≠ v0 := by rintro rfl; exact huA hv0
        have h2 : u ∉ A \ {v0} := fun h => huA (Finset.mem_sdiff.mp h |>.1)
        simp [huA, h1, h2]
    dsimp [π]
    simp only [Finset.sum_add_distrib]
    change (∑ v, if u = x ∧ v = x then γ else 0) +
      (∑ v, if u = x ∧ v = y then 1/2 - γ else 0) +
      (∑ v, if u = y ∧ v = y then γ else 0) +
      (∑ v, if u = v ∧ u ∈ C then γ else 0) +
      (∑ v, if u = v0 ∧ v = u0 then γ else 0) +
      (∑ v, if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else 0) = _
    rw [e1, e2, e3, e4, e5, e6]
    rw [add_assoc ((((if u = x then γ else 0) + if u = x then 1 / 2 - γ else 0) +
          if u = y then γ else 0) + if u ∈ C then γ else 0)]
    rw [e56]
    have hdeg : G.degree x = G.degree y := by rw [hdx, hdy, hAB]
    simp only [graph_idle_measure]
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num]
    dsimp [γ]
    rw [hdeg]
    have hxC : x ∉ C := by rw [hCmem]; simp
    have hxA : x ∉ A := by rw [hAmem]; simp
    have hyC : y ∉ C := by rw [hCmem]; simp
    have hyA : y ∉ A := by rw [hAmem]; simp
    rcases hu_cases u with hux | huy | huA | huB | huC | huP
    · rw [hux]; simp [hxy.ne, hxC, hxA]
    · rw [huy]; simp [hxy.ne.symm, hyC, hyA, hxy]
    · have hm := (hAmem u).mp huA
      have huAx : G.Adj x u := hm.1
      have huAny : ¬ G.Adj y u := hm.2.1
      have huy : u ≠ y := hm.2.2
      have hux : u ≠ x := by rintro rfl; exact G.irrefl hm.1
      have huC : u ∉ C := by rw [hCmem]; exact fun h => huAny h.2
      simp [hux, huy, huC, huA, huAx]
    · have hm := (hBmem u).mp huB
      have huBy : G.Adj y u := hm.1
      have huBnx : ¬ G.Adj x u := hm.2.1
      have hux : u ≠ x := hm.2.2
      have huy : u ≠ y := by rintro rfl; exact G.irrefl huBy
      have huA : u ∉ A := by rw [hAmem]; exact fun h => huBnx h.1
      have huC : u ∉ C := by rw [hCmem]; exact fun h => huBnx h.1
      simp [hux, huy, huC, huA, huBnx]
    · have hm := (hCmem u).mp huC
      have huCx : G.Adj x u := hm.1
      have huCy : G.Adj y u := hm.2
      have hux : u ≠ x := by rintro rfl; exact G.irrefl huCx
      have huy : u ≠ y := by rintro rfl; exact G.irrefl huCy
      have huA : u ∉ A := by rw [hAmem]; exact fun h => h.2.1 huCy
      simp [hux, huy, huC, huA, huCx]
    · have hm := (hPmem u).mp huP
      have huPx : ¬ G.Adj x u := hm.1
      have huPy : ¬ G.Adj y u := hm.2
      have hux : u ≠ x := by rintro rfl; exact huPy hxy.symm
      have huy : u ≠ y := by rintro rfl; exact huPx hxy
      have huA : u ∉ A := by rw [hAmem]; exact fun h => huPx h.1
      have huC : u ∉ C := by rw [hCmem]; exact fun h => huPx h.1
      simp [hux, huy, huC, huA, huPx]
  · intro v
    have hu_cases : ∀ u : V, u = x ∨ u = y ∨ u ∈ A ∨ u ∈ B ∨ u ∈ C ∨ u ∈ P := by
      intro w
      have h : w ∈ (Finset.univ : Finset V) := Finset.mem_univ w
      rw [hcover] at h
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      tauto
    have c1 : (∑ u, if u = x ∧ v = x then γ else (0:ℝ)) = if v = x then γ else 0 := by
      by_cases h : v = x <;> simp [h]
    have c2 : (∑ u, if u = x ∧ v = y then 1/2 - γ else (0:ℝ)) = if v = y then 1/2 - γ else 0 := by
      by_cases h : v = y <;> simp [h]
    have c3 : (∑ u, if u = y ∧ v = y then γ else (0:ℝ)) = if v = y then γ else 0 := by
      by_cases h : v = y <;> simp [h]
    have c4 : (∑ u, if u = v ∧ u ∈ C then γ else (0:ℝ)) = if v ∈ C then γ else 0 := by
      have : (∑ u, if u = v ∧ u ∈ C then γ else (0:ℝ)) = ∑ u, if u = v then (if v ∈ C then γ else 0) else 0 := by
        apply Finset.sum_congr rfl; intro u _; by_cases h : u = v <;> simp [h]
      rw [this]; simp
    have c5 : (∑ u, if u = v0 ∧ v = u0 then γ else (0:ℝ)) = if v = u0 then γ else 0 := by
      by_cases h : v = u0 <;> simp [h]
    have c6 : (∑ u, if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else (0:ℝ)) =
        if v ∈ B \ {u0} then γ else 0 := by
      by_cases hv : v ∈ B \ {u0}
      · simp only [hv, and_true, if_true]
        have huB : v ∈ B := Finset.mem_sdiff.mp hv |>.1
        have hne' : v ≠ u0 := by
          have := Finset.mem_sdiff.mp hv |>.2
          simp only [Finset.mem_singleton] at this
          exact this
        have hB2 : 2 ≤ B.card := by
          have : {v, u0} ⊆ B := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption
          have hle := Finset.card_le_card this
          rw [Finset.card_pair hne'] at hle
          exact hle
        have hdenom : (A.card : ℝ) - 1 ≠ 0 := by
          have : 1 < A.card := by rw [hAB]; exact hB2
          have : (1 : ℝ) < (A.card : ℝ) := Nat.one_lt_cast.mpr this
          linarith
        have hsum : (∑ u, (if u ∈ A \ {v0} then γ / ((A.card : ℝ) - 1) else (0 : ℝ))) =
            ∑ u ∈ A \ {v0}, (γ / ((A.card : ℝ) - 1)) := by
          rw [← Finset.sum_filter]; congr 1; ext u; simp
        rw [hsum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sdiff_singleton_eq_erase, Finset.cast_card_erase_of_mem hv0]
        exact mul_div_cancel₀ γ hdenom
      · simp [hv]
    have c23 : (if v = y then 1/2 - γ else 0) + (if v = y then γ else 0) =
        if v = y then 1/2 else 0 := by
      by_cases h : v = y <;> simp [h]
    have c56 : (if v = u0 then γ else 0) + (if v ∈ B \ {u0} then γ else 0) =
        if v ∈ B then γ else 0 := by
      by_cases hvB : v ∈ B
      · by_cases hvu0 : v = u0
        · subst hvu0; simp [Finset.mem_sdiff, hvB]
        · have : v ∈ B \ {u0} := by
            rw [Finset.mem_sdiff, Finset.mem_singleton]
            exact ⟨hvB, hvu0⟩
          simp [hvu0, this, hvB]
      · have h1 : v ≠ u0 := by rintro rfl; exact hvB hu0
        have h2 : v ∉ B \ {u0} := fun h => hvB (Finset.mem_sdiff.mp h |>.1)
        simp [hvB, h1, h2]
    dsimp [π]
    simp only [Finset.sum_add_distrib]
    change (∑ u, if u = x ∧ v = x then γ else 0) +
      (∑ u, if u = x ∧ v = y then 1/2 - γ else 0) +
      (∑ u, if u = y ∧ v = y then γ else 0) +
      (∑ u, if u = v ∧ u ∈ C then γ else 0) +
      (∑ u, if u = v0 ∧ v = u0 then γ else 0) +
      (∑ u, if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else 0) = _
    rw [c1, c2, c3, c4, c5, c6]
    rw [add_assoc (if v = x then γ else 0)]
    rw [c23]
    rw [add_assoc ((if v = x then γ else 0) + (if v = y then 1 / 2 else 0) + (if v ∈ C then γ else 0))]
    rw [c56]
    simp only [graph_idle_measure]
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num]
    dsimp [γ]
    have hxB : x ∉ B := by rw [hBmem]; simp
    have hxC : x ∉ C := by rw [hCmem]; simp
    have hyB : y ∉ B := by rw [hBmem]; simp
    have hyC : y ∉ C := by rw [hCmem]; simp
    rcases hu_cases v with hvx | hvy | hvA | hvB | hvC | hvP
    · rw [hvx]; simp [hxy.ne, hxy.symm, hxB, hxC]
    · rw [hvy]; simp [hxy.ne.symm, hyB, hyC]
    · have hm := (hAmem v).mp hvA
      have hvAx : G.Adj x v := hm.1
      have hvAny : ¬ G.Adj y v := hm.2.1
      have hvy : v ≠ y := hm.2.2
      have hvx : v ≠ x := by rintro rfl; exact G.irrefl hm.1
      have hvB : v ∉ B := by rw [hBmem]; exact fun h => hvAny h.1
      have hvC : v ∉ C := by rw [hCmem]; exact fun h => hvAny h.2
      simp [hvx, hvy, hvB, hvC, hvAny]
    · have hm := (hBmem v).mp hvB
      have hvBy : G.Adj y v := hm.1
      have hvBnx : ¬ G.Adj x v := hm.2.1
      have hvx : v ≠ x := hm.2.2
      have hvy : v ≠ y := by rintro rfl; exact G.irrefl hvBy
      have hvC : v ∉ C := by rw [hCmem]; exact fun h => hvBnx h.1
      simp [hvx, hvy, hvC, hvB, hvBy]
    · have hm := (hCmem v).mp hvC
      have hvCx : G.Adj x v := hm.1
      have hvCy : G.Adj y v := hm.2
      have hvx : v ≠ x := by rintro rfl; exact G.irrefl hvCx
      have hvy : v ≠ y := by rintro rfl; exact G.irrefl hvCy
      have hvB : v ∉ B := by rw [hBmem]; exact fun h => h.2.1 hvCx
      simp [hvx, hvy, hvC, hvB, hvCy]
    · have hm := (hPmem v).mp hvP
      have hvPx : ¬ G.Adj x v := hm.1
      have hvPy : ¬ G.Adj y v := hm.2
      have hvx : v ≠ x := by rintro rfl; exact hvPy hxy.symm
      have hvy : v ≠ y := by rintro rfl; exact hvPx hxy
      have hvB : v ∉ B := by rw [hBmem]; exact fun h => hvPy h.1
      have hvC : v ∉ C := by rw [hCmem]; exact fun h => hvPx h.1
      simp [hvx, hvy, hvC, hvB, hvPy]
  · have hdist2 (u v : V) : (G.dist u v : ℝ) ≤ 2 := by
      exact_mod_cast graph_dist_le_two_of_ediam_le_two G hdiam u v
    have hAdenom : (0:ℝ) ≤ (A.card : ℝ) - 1 := by
      have : (1:ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hne
      linarith
    have hγnn : (0:ℝ) ≤ γ := div_nonneg (by norm_num) (by positivity)
    have hT6nn (u v : V) : (0:ℝ) ≤ (if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else 0) := by
      split_ifs; exact div_nonneg hγnn hAdenom; rfl

    have hle_pointwise (u v : V) :
        (G.dist u v : ℝ) * π u v ≤
          (if u = x ∧ v = y then 1/2 - γ else 0) +
          (if u = v0 ∧ v = u0 then γ else 0) +
          2 * (if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else 0) := by
      have hd1 : (G.dist u v : ℝ) * (if u = x ∧ v = x then γ else 0) = 0 := by
        by_cases h : u = x ∧ v = x
        · rw [h.1, h.2]; simp
        · simp [h]
      have hd2 : (G.dist u v : ℝ) * (if u = x ∧ v = y then 1/2 - γ else 0) =
          (if u = x ∧ v = y then 1/2 - γ else 0) := by
        by_cases h : u = x ∧ v = y
        · rw [h.1, h.2]
          have hd : (G.dist x y : ℝ) = 1 := by simp [SimpleGraph.dist_eq_one_iff_adj.mpr hxy]
          simp [hd]
        · simp [h]
      have hd3 : (G.dist u v : ℝ) * (if u = y ∧ v = y then γ else 0) = 0 := by
        by_cases h : u = y ∧ v = y
        · rw [h.1, h.2]; simp
        · simp [h]
      have hd4 : (G.dist u v : ℝ) * (if u = v ∧ u ∈ C then γ else 0) = 0 := by
        by_cases h : u = v ∧ u ∈ C
        · rw [h.1]; simp
        · simp [h]
      have hd5 : (G.dist u v : ℝ) * (if u = v0 ∧ v = u0 then γ else 0) =
          (if u = v0 ∧ v = u0 then γ else 0) := by
        by_cases h : u = v0 ∧ v = u0
        · rw [h.1, h.2]
          have hd : (G.dist v0 u0 : ℝ) = 1 := by simp [SimpleGraph.dist_eq_one_iff_adj.mpr hadj0]
          simp [hd]
        · simp [h]
      have hd6 : (G.dist u v : ℝ) * (if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else 0) ≤
          2 * (if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else 0) :=
        mul_le_mul_of_nonneg_right (hdist2 u v) (hT6nn u v)
      dsimp [π]
      linarith

    have hsum_le : (∑ u, ∑ v, (G.dist u v : ℝ) * π u v) ≤
        ∑ u, ∑ v, ((if u = x ∧ v = y then 1/2 - γ else 0) +
          (if u = v0 ∧ v = u0 then γ else 0) +
          2 * (if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else 0)) :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hle_pointwise u v
    apply hsum_le.trans
    simp_rw [Finset.sum_add_distrib]
    have hsum1 : (∑ u, ∑ v, if u = x ∧ v = y then 1/2 - γ else (0:ℝ)) = 1/2 - γ := by
      have h (u v : V) : (if u = x ∧ v = y then 1/2 - γ else (0 : ℝ)) =
          (if u = x then if v = y then 1/2 - γ else 0 else 0) := by
        split_ifs <;> tauto
      simp_rw [h]; simp
    have hsum2 : (∑ u, ∑ v, if u = v0 ∧ v = u0 then γ else (0:ℝ)) = γ := by
      have h (u v : V) : (if u = v0 ∧ v = u0 then γ else (0 : ℝ)) =
          (if u = v0 then if v = u0 then γ else 0 else 0) := by
        split_ifs <;> tauto
      simp_rw [h]; simp
    have hsum3 : (∑ u, ∑ v, 2 * (if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else (0:ℝ))) =
        2 * ((A.card : ℝ) - 1) * γ := by
      simp_rw [← Finset.mul_sum]
      have hstep (u : V) : (∑ v, if u ∈ A \ {v0} ∧ v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else (0:ℝ)) =
          if u ∈ A \ {v0} then γ else 0 := by
        by_cases hu : u ∈ A \ {v0}
        · simp only [hu, true_and, if_true]
          have huA : u ∈ A := Finset.mem_sdiff.mp hu |>.1
          have hne' : u ≠ v0 := by
            have := Finset.mem_sdiff.mp hu |>.2
            simp only [Finset.mem_singleton] at this
            exact this
          have hA2 : 2 ≤ A.card := by
            have : {u, v0} ⊆ A := by
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl <;> assumption
            have hle := Finset.card_le_card this
            rw [Finset.card_pair hne'] at hle
            exact hle
          have hdenom : (A.card : ℝ) - 1 ≠ 0 := by
            have : 1 < A.card := hA2
            have : (1 : ℝ) < (A.card : ℝ) := Nat.one_lt_cast.mpr this
            linarith
          have hsum : (∑ v, (if v ∈ B \ {u0} then γ / ((A.card : ℝ) - 1) else (0 : ℝ))) =
              ∑ v ∈ B \ {u0}, (γ / ((A.card : ℝ) - 1)) := by
            rw [← Finset.sum_filter]; congr 1; ext v; simp
          rw [hsum]
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.sdiff_singleton_eq_erase, Finset.cast_card_erase_of_mem hu0, ← hAB]
          exact mul_div_cancel₀ γ hdenom
        · simp [hu]
      simp_rw [hstep]
      have hsum : (∑ u, if u ∈ A \ {v0} then γ else (0 : ℝ)) = ∑ u ∈ A \ {v0}, γ := by
        rw [← Finset.sum_filter]; congr 1; ext u; simp
      rw [hsum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sdiff_singleton_eq_erase, Finset.cast_card_erase_of_mem hv0]
      ring
    rw [hsum1, hsum2, hsum3]
    dsimp [γ]
    linarith
