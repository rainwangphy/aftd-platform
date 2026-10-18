import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIdleTransportPlanMain
import AFTD.Kb.Tcs.GraphEdgePartitionCard
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_idle_transport_plan_main_marginals

Topic: graphs   Node: c38d46b78e6d

Provenance: helper lemma. step towards exists_idle_measure_wasserstein_dist_lt_one_of_ediam_le_two_and_minDegree_ge

With β = (1/2)/d_x, γ = (1/2)/d_y and d_x ≤ d_y, A.card ≤ B.card, the main plan has nonnegative entries, row sums μ_x^{1/2} and column sums μ_y^{1/2}.
-/

/-- The main plan is nonnegative and has the prescribed marginals. -/
theorem graph_idle_transport_plan_main_marginals {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : G.Adj x y)
    (A B C P : Finset V)
    (hAmem : ∀ v, v ∈ A ↔ (G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y))
    (hBmem : ∀ v, v ∈ B ↔ (G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x))
    (hCmem : ∀ v, v ∈ C ↔ (G.Adj x v ∧ G.Adj y v))
    (hPmem : ∀ v, v ∈ P ↔ (¬ G.Adj x v ∧ ¬ G.Adj y v))
    (hcover : (Finset.univ : Finset V) = {x} ∪ {y} ∪ A ∪ B ∪ C ∪ P)
    (hdx : G.degree x = A.card + C.card + 1)
    (hdy : G.degree y = B.card + C.card + 1)
    (hle : G.degree x ≤ G.degree y) (hab : A.card ≤ B.card) :
    (∀ u v, 0 ≤ graph_idle_transport_plan_main G x y A B C u v) ∧
      (∀ u, ∑ v, graph_idle_transport_plan_main G x y A B C u v =
        graph_idle_measure G (1/2) x u) ∧
      (∀ v, ∑ u, graph_idle_transport_plan_main G x y A B C u v =
        graph_idle_measure G (1/2) y v) := by
  classical
  have hdxpos : (0:ℝ) < (G.degree x : ℝ) := by
    have : 0 < G.degree x := by
      rw [SimpleGraph.degree_pos_iff_exists_adj]; exact ⟨y, hxy⟩
    exact_mod_cast this
  have hγβ : (1/2)/(G.degree y : ℝ) ≤ (1/2)/(G.degree x : ℝ) := by
    have hleR : (G.degree x : ℝ) ≤ (G.degree y : ℝ) := by exact_mod_cast hle
    exact div_le_div_of_nonneg_left (by norm_num) hdxpos hleR
  have hβle : (1/2)/(G.degree x : ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hdxpos]
    have h1 : (1:ℝ) ≤ (G.degree x : ℝ) := by
      have : 0 < G.degree x := by
        rw [SimpleGraph.degree_pos_iff_exists_adj]; exact ⟨y, hxy⟩
      exact_mod_cast this
    linarith
  have hABcard : A.card ≤ B.card := hab
  have hBempty_beta : B = ∅ → (1/2)/(G.degree x : ℝ) = (1/2)/(G.degree y : ℝ) := by
    intro hB
    have hB0 : B.card = 0 := by rw [hB]; simp
    have hA0 : A.card = 0 := by omega
    have hdeg : G.degree x = G.degree y := by rw [hdx, hdy, hA0, hB0]
    rw [hdeg]
  have hBne_of_memA : ∀ u : V, u ∈ A → B.Nonempty := by
    intro u hu
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨u, hu⟩
    exact Finset.card_pos.mp (lt_of_lt_of_le hApos hABcard)
  have hu_cases : ∀ u : V, u = x ∨ u = y ∨ u ∈ A ∨ u ∈ B ∨ u ∈ C ∨ u ∈ P := by
    intro u
    have h : u ∈ (Finset.univ : Finset V) := Finset.mem_univ u
    rw [hcover] at h
    simp only [Finset.mem_union, Finset.mem_singleton] at h
    tauto
  have hxnotC : x ∉ C := by rw [hCmem]; simp
  have hdisj : ∀ u : V, u ∈ A → ¬ (u = x ∨ u ∈ C) := by
    intro u huA hP
    have hm := (hAmem u).mp huA
    have huAny : ¬ G.Adj y u := hm.2.1
    rcases hP with h | h
    · rw [h] at huAny; exact huAny hxy.symm
    · exact huAny ((hCmem u).mp h).2
  have hfilter : (Finset.univ.filter (fun u : V => u = x ∨ u ∈ C)) = insert x C := by
    ext u
    simp [Finset.mem_insert]
  have hPsum : (∑ u : V, (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ) else 0))
      = ((C.card:ℝ)+1) * ((1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ)) := by
    rw [← Finset.sum_filter]
    rw [hfilter]
    rw [Finset.sum_insert hxnotC]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hAsum : (∑ u : V, (if u ∈ A then (1/2)/(G.degree x : ℝ) else 0))
      = (A.card:ℝ) * ((1/2)/(G.degree x : ℝ)) := by
    rw [← Finset.sum_filter]
    have hf : (Finset.univ.filter (fun u : V => u ∈ A)) = A := by ext u; simp
    rw [hf, Finset.sum_const, nsmul_eq_mul]
  have hkey : (A.card : ℝ) * ((1/2)/(G.degree x : ℝ))
      + ((C.card : ℝ) + 1) * ((1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ))
      = (B.card : ℝ) * ((1/2)/(G.degree y : ℝ)) := by
    have hdxR : (G.degree x : ℝ) = (A.card : ℝ) + (C.card : ℝ) + 1 := by
      rw [hdx]; push_cast; ring
    have hdyR : (G.degree y : ℝ) = (B.card : ℝ) + (C.card : ℝ) + 1 := by
      rw [hdy]; push_cast; ring
    rw [hdxR, hdyR]
    field_simp
    ring
  have hpoint : ∀ u : V, (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ)
      else if u ∈ A then (1/2)/(G.degree x : ℝ) else 0)
      = (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ) else 0)
        + (if u ∈ A then (1/2)/(G.degree x : ℝ) else 0) := by
    intro u
    by_cases hP : u = x ∨ u ∈ C
    · have hAn : u ∉ A := fun hA => hdisj u hA hP
      simp [hP, hAn]
    · by_cases hA : u ∈ A
      · simp [hP, hA]
      · simp [hP, hA]
  have hsum : (∑ u : V, (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ)
      else if u ∈ A then (1/2)/(G.degree x : ℝ) else 0))
      = (B.card:ℝ) * ((1/2)/(G.degree y : ℝ)) := by
    calc (∑ u : V, (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ)
        else if u ∈ A then (1/2)/(G.degree x : ℝ) else 0))
        = ∑ u : V, ((if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ) else 0)
            + (if u ∈ A then (1/2)/(G.degree x : ℝ) else 0)) := by
          apply Finset.sum_congr rfl; intro u _; exact hpoint u
      _ = (∑ u : V, (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ) else 0))
            + (∑ u : V, (if u ∈ A then (1/2)/(G.degree x : ℝ) else 0)) := by
          rw [Finset.sum_add_distrib]
      _ = ((C.card:ℝ)+1) * ((1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ))
            + (A.card:ℝ) * ((1/2)/(G.degree x : ℝ)) := by rw [hPsum, hAsum]
      _ = (B.card:ℝ) * ((1/2)/(G.degree y : ℝ)) := by linarith [hkey]
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    have hγnn : (0:ℝ) ≤ (1/2)/(G.degree y : ℝ) := div_nonneg (by norm_num) (by positivity)
    have hβnn : (0:ℝ) ≤ (1/2)/(G.degree x : ℝ) := div_nonneg (by norm_num) (by positivity)
    have hβγnn : (0:ℝ) ≤ (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ) := by linarith
    simp only [graph_idle_transport_plan_main]
    apply add_nonneg
    apply add_nonneg
    apply add_nonneg
    · by_cases h : u = x ∧ v = x
      · simp only [h, if_true]; exact hγnn
      · simp [h]
    · by_cases hvy : v = y
      · simp only [hvy, if_true]
        by_cases hux : u = x
        · simp only [hux, if_true]; linarith
        · simp only [hux, if_false]
          by_cases huy : u = y
          · simp only [huy, if_true]; exact hβnn
          · simp [huy]
      · simp [hvy]
    · by_cases h : u = v
      · rw [if_pos h]
        by_cases hC : u ∈ C
        · simp only [hC, if_true]; exact hγnn
        · simp [hC]
      · simp [h]
    · by_cases hB : v ∈ B
      · simp only [hB, if_true]
        by_cases hP : u = x ∨ u ∈ C
        · simp only [hP, if_true]; exact div_nonneg hβγnn (by positivity)
        · simp only [hP, if_false]
          by_cases hA : u ∈ A
          · simp only [hA, if_true]; exact div_nonneg hβnn (by positivity)
          · simp [hA]
      · simp [hB]
  · intro u
    have e1 : (∑ v, (if u = x ∧ v = x then (1/2)/(G.degree y : ℝ) else 0))
        = (if u = x then (1/2)/(G.degree y : ℝ) else 0) := by
      by_cases h : u = x
      · subst h; simp
      · simp [h]
    have e2 : (∑ v, (if v = y then (if u = x then 1/2 - (1/2)/(G.degree x : ℝ)
        else if u = y then (1/2)/(G.degree x : ℝ) else 0) else 0))
        = (if u = x then 1/2 - (1/2)/(G.degree x : ℝ)
        else if u = y then (1/2)/(G.degree x : ℝ) else 0) := by
      simp
    have e3 : (∑ v, (if u = v then (if u ∈ C then (1/2)/(G.degree y : ℝ) else 0) else 0))
        = (if u ∈ C then (1/2)/(G.degree y : ℝ) else 0) := by
      simp
    have e4 : (∑ v, (if v ∈ B then (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ)
        else if u ∈ A then (1/2)/(G.degree x : ℝ) else 0) / (B.card : ℝ) else 0))
        = if B.Nonempty then (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ)
        else if u ∈ A then (1/2)/(G.degree x : ℝ) else 0) else 0 := by
      rw [Finset.sum_ite_mem]
      simp only [Finset.univ_inter]
      by_cases h : B = ∅
      · subst h; simp
      · have hc : (B.card : ℝ) ≠ 0 := by
          have : 0 < B.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
          exact_mod_cast ne_of_gt this
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [h, hc, div_eq_mul_inv, mul_comm]
    simp only [graph_idle_transport_plan_main, Finset.sum_add_distrib]
    rw [e1, e2, e3, e4]
    simp only [graph_idle_measure]
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num]
    rcases hu_cases u with hux | huy | huA | huB | huC | huP
    · rw [hux] at *
      have hxC : x ∉ C := by rw [hCmem]; simp
      by_cases hB : B = ∅
      · have hβγ := hBempty_beta hB
        simp [hB, hxC]
        linarith
      · have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
        simp [hBne, hxC] <;> ring
    · rw [huy] at *
      have hyC : y ∉ C := by rw [hCmem]; simp
      have hyA : y ∉ A := by rw [hAmem]; simp
      by_cases hBne : B.Nonempty
      · simp [hBne, hxy, hxy.ne.symm, hyC, hyA] <;> ring
      · simp [hBne, hxy, hxy.ne.symm, hyC, hyA] <;> ring
    · have hBne : B.Nonempty := hBne_of_memA u huA
      have hm := (hAmem u).mp huA
      have huAx : G.Adj x u := hm.1
      have huAny : ¬ G.Adj y u := hm.2.1
      have huy : u ≠ y := hm.2.2
      have hux : u ≠ x := by intro h; subst h; exact huAny hxy.symm
      have huC : u ∉ C := by rw [hCmem]; exact fun h => huAny h.2
      simp [huA, hBne, huC, hux, huy, huAx] <;> ring
    · have huBne : B.Nonempty := ⟨u, huB⟩
      have hm := (hBmem u).mp huB
      have huBy : G.Adj y u := hm.1
      have huBnx : ¬ G.Adj x u := hm.2.1
      have hux : u ≠ x := hm.2.2
      have huy : u ≠ y := by intro h; subst h; exact G.irrefl huBy
      have huA : u ∉ A := by rw [hAmem]; exact fun h => huBnx h.1
      have huC : u ∉ C := by rw [hCmem]; exact fun h => huBnx h.1
      simp [huBne, huBnx, huA, huC, hux, huy] <;> ring
    · have hCm := (hCmem u).mp huC
      have huCx : G.Adj x u := hCm.1
      have huCy : G.Adj y u := hCm.2
      have hux : u ≠ x := by intro h; subst h; exact G.irrefl huCx
      have huy : u ≠ y := by intro h; subst h; exact G.irrefl huCy
      by_cases hB : B = ∅
      · have hβγ := hBempty_beta hB
        simp [hB, huC, hux, huy, huCx]
        linarith
      · have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
        simp [hBne, huC, hux, huy, huCx] <;> ring
    · have hm := (hPmem u).mp huP
      have huPx : ¬ G.Adj x u := hm.1
      have huPy : ¬ G.Adj y u := hm.2
      have hux : u ≠ x := by intro h; subst h; exact huPy hxy.symm
      have huy : u ≠ y := by intro h; subst h; exact huPx hxy
      have huA : u ∉ A := by rw [hAmem]; exact fun h => huPx h.1
      have huC : u ∉ C := by rw [hCmem]; exact fun h => huPx h.1
      by_cases hBne : B.Nonempty
      · simp [hBne, huPx, huA, huC, hux, huy] <;> ring
      · simp [hBne, huPx, huA, huC, hux, huy] <;> ring
  · intro v
    have c1 : (∑ u, (if u = x ∧ v = x then (1/2)/(G.degree y : ℝ) else 0))
        = if v = x then (1/2)/(G.degree y : ℝ) else 0 := by
      by_cases hv : v = x
      · rw [hv]; simp
      · simp [hv]
    have c2 : (∑ u, (if v = y then (if u = x then 1/2 - (1/2)/(G.degree x : ℝ)
        else if u = y then (1/2)/(G.degree x : ℝ) else 0) else 0))
        = if v = y then 1/2 else 0 := by
      by_cases hv : v = y
      · rw [hv]
        have hne : x ≠ y := hxy.ne
        have step : ∑ u : V, (if u = x then 1/2 - (1/2)/(G.degree x : ℝ)
            else if u = y then (1/2)/(G.degree x : ℝ) else 0)
            = (∑ u, (if u = x then 1/2 - (1/2)/(G.degree x : ℝ) else 0))
              + ∑ u, (if u = y then (1/2)/(G.degree x : ℝ) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro u _
          by_cases h1 : u = x
          · subst h1; simp [hne]
          · by_cases h2 : u = y
            · subst h2; simp [h1]
            · simp [h1, h2]
        simp only [if_true]
        rw [step]
        simp
      · simp [hv]
    have c3 : (∑ u, (if u = v then (if u ∈ C then (1/2)/(G.degree y : ℝ) else 0) else 0))
        = (if v ∈ C then (1/2)/(G.degree y : ℝ) else 0) := by
      simp
    have c4 : (∑ u, (if v ∈ B then (if (u = x ∨ u ∈ C) then (1/2)/(G.degree x : ℝ) - (1/2)/(G.degree y : ℝ)
        else if u ∈ A then (1/2)/(G.degree x : ℝ) else 0) / (B.card : ℝ) else 0))
        = if v ∈ B then (1/2)/(G.degree y : ℝ) else 0 := by
      by_cases hv : v ∈ B
      · simp only [hv, if_true]
        rw [← Finset.sum_div, hsum]
        have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨v, hv⟩
        have hBc : (B.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hBpos
        field_simp
      · simp [hv]
    simp only [graph_idle_transport_plan_main, Finset.sum_add_distrib]
    rw [c1, c2, c3, c4]
    simp only [graph_idle_measure]
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num]
    rcases hu_cases v with hvx | hvy | hvA | hvB | hvC | hvP
    · rw [hvx] at *
      have hxB : x ∉ B := by rw [hBmem]; simp
      simp [hxnotC, hxB, hxy.ne, hxy.symm]
    · rw [hvy] at *
      have hyC : y ∉ C := by rw [hCmem]; simp
      have hyB : y ∉ B := by rw [hBmem]; simp
      simp [hyC, hyB, hxy.ne.symm]
    · have hm := (hAmem v).mp hvA
      have hvAny : ¬G.Adj y v := hm.2.1
      have hvy : v ≠ y := hm.2.2
      have hvx : v ≠ x := by intro h; rw [h] at hm; exact G.irrefl hm.1
      have hvB : v ∉ B := by rw [hBmem]; exact fun h => hvAny h.1
      have hvC : v ∉ C := by rw [hCmem]; exact fun h => hvAny h.2
      simp [hvAny, hvx, hvy, hvB, hvC]
    · have hm := (hBmem v).mp hvB
      have hvBy : G.Adj y v := hm.1
      have hvBnx : ¬G.Adj x v := hm.2.1
      have hvx : v ≠ x := hm.2.2
      have hvy : v ≠ y := by intro h; rw [h] at hvBy; exact G.irrefl hvBy
      have hvC : v ∉ C := by rw [hCmem]; exact fun h => hvBnx h.1
      simp [hvB, hvBy, hvx, hvy, hvC]
    · have hm := (hCmem v).mp hvC
      have hvCx : G.Adj x v := hm.1
      have hvCy : G.Adj y v := hm.2
      have hvx : v ≠ x := by intro h; rw [h] at hvCx; exact G.irrefl hvCx
      have hvy : v ≠ y := by intro h; rw [h] at hvCy; exact G.irrefl hvCy
      have hvB : v ∉ B := by rw [hBmem]; exact fun h => h.2.1 hvCx
      simp [hvC, hvB, hvCy, hvx, hvy]
    · have hm := (hPmem v).mp hvP
      have hvPx : ¬G.Adj x v := hm.1
      have hvPy : ¬G.Adj y v := hm.2
      have hvx : v ≠ x := by intro h; rw [h] at hvPy; exact hvPy hxy.symm
      have hvy : v ≠ y := by intro h; rw [h] at hvPx; exact hvPx hxy
      have hvB : v ∉ B := by rw [hBmem]; exact fun h => hvPy h.1
      have hvC : v ∉ C := by rw [hCmem]; exact fun h => hvPx h.1
      simp [hvPy, hvx, hvy, hvB, hvC]
