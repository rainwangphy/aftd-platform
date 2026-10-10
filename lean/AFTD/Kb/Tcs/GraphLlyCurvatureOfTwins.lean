import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureEqOfOllivierEq
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan
import AFTD.Kb.Tcs.GraphWassersteinDistGeOfLipschitz
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg
import AFTD.Kb.Tcs.GraphIdleMeasureSumEqOne
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphLlyCurvatureOfLeaf
import AFTD.Kb.Tcs.GraphOllivierCurvature

/-!
# graph_lly_curvature_of_twins

Topic: graphs   Node: 13af14f9065a

Provenance: helper lemma. Helper for the refutation of OP-165 (arXiv:2610.10559, after Theorem 1.4). Generalizes κ_LLY = n/(n−1) on the complete graph K_n.

If x and y are adjacent and have the same neighbours apart from each other, then κ_LLY(x, y) = (d_x + 1)/d_x.
-/

theorem graph_lly_curvature_of_twins {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (x y : V) (hxy : G.Adj x y)
    (htw : ∀ w, w ≠ x → w ≠ y → (G.Adj x w ↔ G.Adj y w)) :
    graph_lly_curvature G x y = ((G.degree x : ℝ) + 1) / (G.degree x : ℝ) := by
  have hne : x ≠ y := G.ne_of_adj hxy
  have hxN : x ∈ G.neighborFinset y := by simpa [SimpleGraph.mem_neighborFinset] using hxy.symm
  have hyN : y ∈ G.neighborFinset x := by simpa [SimpleGraph.mem_neighborFinset] using hxy
  have hdeg : G.degree y = G.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hs : (G.neighborFinset y).erase x = (G.neighborFinset x).erase y := by
      ext w; simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hwx, hyw⟩
        have hwy : w ≠ y := fun h => G.irrefl (h ▸ hyw)
        exact ⟨hwy, (htw w hwx hwy).mpr hyw⟩
      · rintro ⟨hwy, hxw⟩
        have hwx : w ≠ x := fun h => G.irrefl (h ▸ hxw)
        exact ⟨hwx, (htw w hwx hwy).mp hxw⟩
    have c1 := Finset.card_erase_of_mem hxN
    have c2 := Finset.card_erase_of_mem hyN
    rw [hs] at c1
    have p1 : 0 < (G.neighborFinset y).card := Finset.card_pos.mpr ⟨x, hxN⟩
    have p2 : 0 < (G.neighborFinset x).card := Finset.card_pos.mpr ⟨y, hyN⟩
    omega
  have hDpos : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
  have hDR : (0 : ℝ) < G.degree x := by exact_mod_cast hDpos
  have hdxy : G.dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxy
  apply graph_lly_curvature_eq_of_ollivier_eq G x y _ (1/2) (by norm_num)
  intro α hα1 hα2
  set q : ℝ := (1 - α) / (G.degree x : ℝ) with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hDR.le
  have hqle : q ≤ 1 - α := by
    rw [hq, div_le_iff₀ hDR]
    have : (1 : ℝ) ≤ G.degree x := by exact_mod_cast hDpos
    nlinarith
  have hμx : ∀ b, graph_idle_measure G α x b = if b = x then α else if G.Adj x b then q else 0 := by
    intro b; rfl
  have hμy : ∀ b, graph_idle_measure G α y b = if b = y then α else if G.Adj y b then q else 0 := by
    intro b; simp only [graph_idle_measure, hdeg, hq]
  have hsx : ∑ b, graph_idle_measure G α x b = 1 := graph_idle_measure_sum_eq_one G α x hDpos
  have hsy : ∑ b, graph_idle_measure G α y b = 1 :=
    graph_idle_measure_sum_eq_one G α y (by rw [hdeg]; exact hDpos)
  set f : V → ℝ := fun b => if b = x then 1 else 0 with hf
  have hfge : ∀ a b, f a - f b ≤ (G.dist a b : ℝ) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    have h1 : (1 : ℝ) ≤ G.dist a b := by exact_mod_cast hG.pos_dist_of_ne hab
    simp only [hf]
    split_ifs <;> linarith
  have hW : graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y)
      = α - q := by
    apply le_antisymm
    · set m : V → ℝ := fun a => if a = x then q else graph_idle_measure G α x a with hm
      set π : V → V → ℝ := fun a b =>
        (if a = x then (if b = y then α - q else 0) else 0) + (if a = b then m a else 0) with hπ
      have hm0 : ∀ a, 0 ≤ m a := by
        intro a; simp only [hm]; split_ifs
        · exact hq0
        · exact graph_idle_measure_nonneg G α (by linarith) hα2.le x a
      have h0 : ∀ a b, 0 ≤ π a b := by
        intro a b
        simp only [hπ]
        have := hm0 a
        split_ifs <;> linarith
      have hc : ∀ a b, (G.dist a b : ℝ) * π a b =
          if a = x then (if b = y then α - q else 0) else 0 := by
        intro a b
        simp only [hπ]
        by_cases hab : a = b
        · subst hab
          by_cases hax : a = x
          · subst a; simp [hne]
          · simp [hax]
        · rw [if_neg hab, add_zero]
          by_cases hax : a = x
          · subst a
            by_cases hby : b = y
            · subst b; simp [hdxy]
            · simp [hby]
          · simp [hax]
      calc graph_wasserstein_dist G _ _ ≤ ∑ a, ∑ b, (G.dist a b : ℝ) * π a b := by
            apply graph_wasserstein_dist_le_of_plan G _ _ π h0
            · intro a
              simp only [hπ]
              rw [Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero]
              simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
              by_cases hax : a = x
              · subst a; simp [hm, hμx]
              · simp [hax, hm]
            · intro b
              simp only [hπ]
              rw [Finset.sum_add_distrib]
              simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
              by_cases hby : b = y
              · subst b; simp [hm, hμx, hμy, hne.symm, hxy]
              by_cases hbx : b = x
              · subst b; simp [hm, hμy, hne, hxy.symm]
              simp only [if_neg hby, hm, if_neg hbx, zero_add, hμx, hμy]
              simp only [htw b hbx hby]
        _ = α - q := by
            simp_rw [hc]
            rw [Fintype.sum_eq_single x (fun a ha => by simp [ha])]
            simp
    · have := graph_wasserstein_dist_ge_of_lipschitz G _ _
        (graph_idle_measure_nonneg G α (by linarith) hα2.le x)
        (graph_idle_measure_nonneg G α (by linarith) hα2.le y) hsx hsy f hfge
      have e1 : ∑ a, f a * graph_idle_measure G α x a = α := by
        simp only [hf, ite_mul, one_mul, zero_mul]
        simp [hμx]
      have e2 : ∑ a, f a * graph_idle_measure G α y a = q := by
        simp only [hf, ite_mul, one_mul, zero_mul]
        simp [hμy, hne, hxy.symm]
      rw [e1, e2] at this
      exact this
  unfold graph_ollivier_curvature
  rw [hW, hdxy, hq]
  simp only [Nat.cast_one, div_one]
  field_simp
  ring
