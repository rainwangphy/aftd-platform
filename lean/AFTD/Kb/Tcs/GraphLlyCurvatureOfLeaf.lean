import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureEqOfOllivierEq
import AFTD.Kb.Tcs.GraphWassersteinDistLeOfPlan
import AFTD.Kb.Tcs.GraphWassersteinDistGeOfLipschitz
import AFTD.Kb.Tcs.GraphIdleMeasureNonneg
import AFTD.Kb.Tcs.GraphIdleMeasureSumEqOne
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphIdleMeasure
import AFTD.Kb.Tcs.GraphOllivierCurvature

/-!
# graph_lly_curvature_of_leaf

Topic: graphs   Node: 1ef9797a262c

Provenance: helper lemma. Helper for the refutation of OP-165 (arXiv:2610.10559, after Theorem 1.4). The value is the known tree formula 2/d_x + 2/d_y − 2 for d_x = 1.

If x is a leaf of a finite connected graph whose only neighbour is y, then κ_LLY(x, y) = 2/d_y.
-/

theorem graph_lly_curvature_of_leaf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (x y : V) (hxy : G.Adj x y)
    (hleaf : ∀ w, G.Adj x w → w = y) :
    graph_lly_curvature G x y = 2 / (G.degree y : ℝ) := by
  have hDpos : 0 < G.degree y := (G.degree_pos_iff_exists_adj y).mpr ⟨x, hxy.symm⟩
  have hDR : (0 : ℝ) < G.degree y := by exact_mod_cast hDpos
  have hdegx : G.degree x = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : G.neighborFinset x = {y} := by
      ext w; simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      exact ⟨hleaf w, fun h => h ▸ hxy⟩
    rw [this, Finset.card_singleton]
  have hne : x ≠ y := G.ne_of_adj hxy
  have hdxy : G.dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxy
  set f : V → ℝ := fun b => if b = x then 0 else if b = y then 1 else 2 with hf
  have hfle : ∀ b, G.Adj y b → (G.dist x b : ℝ) ≤ f b := by
    intro b hb
    by_cases hbx : b = x
    · subst b; simp [hf]
    by_cases hby : b = y
    · subst b; exact absurd hb G.irrefl
    simp only [hf, if_neg hbx, if_neg hby]
    have : G.dist x b ≤ 2 := by
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons hxy (SimpleGraph.Walk.cons hb SimpleGraph.Walk.nil))
      simpa using this
    exact_mod_cast this
  have hfge : ∀ a b, -f a - -f b ≤ (G.dist a b : ℝ) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    have h1 : 1 ≤ G.dist a b := hG.pos_dist_of_ne hab
    have h1' : (1 : ℝ) ≤ G.dist a b := by exact_mod_cast h1
    by_cases hax : a = x
    · subst a
      by_cases hby : b = y
      · subst b; simp [hf, hne.symm]; linarith
      have hbx : b ≠ x := fun h => hab h.symm
      have hnadj : ¬ G.Adj x b := fun h => hby (hleaf b h)
      have h2 : 2 ≤ G.dist x b := by
        have : G.dist x b ≠ 1 := fun h => hnadj (SimpleGraph.dist_eq_one_iff_adj.mp h)
        omega
      have h2' : (2 : ℝ) ≤ G.dist x b := by exact_mod_cast h2
      simp [hf, hbx, hby]; linarith
    · simp only [hf, if_neg hax]
      split_ifs <;> linarith
  apply graph_lly_curvature_eq_of_ollivier_eq G x y _ (1/2) (by norm_num)
  intro α hα1 hα2
  set q : ℝ := (1 - α) / (G.degree y : ℝ) with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hDR.le
  have hμy : ∀ b, graph_idle_measure G α y b = if b = y then α else if G.Adj y b then q else 0 := by
    intro b; rfl
  have hμx : ∀ b, graph_idle_measure G α x b =
      if b = x then α else if b = y then 1 - α else 0 := by
    intro b
    unfold graph_idle_measure
    by_cases hbx : b = x
    · simp [hbx]
    by_cases hby : b = y
    · subst b; simp [hbx, hxy, hdegx]
    rw [if_neg hbx, if_neg hbx, if_neg hby, if_neg (fun h => hby (hleaf b h))]
  have hsy : ∑ b, graph_idle_measure G α y b = 1 := graph_idle_measure_sum_eq_one G α y hDpos
  have hsx : ∑ b, graph_idle_measure G α x b = 1 :=
    graph_idle_measure_sum_eq_one G α x (by omega)
  have Sx : ∑ b, f b * graph_idle_measure G α x b = 1 - α := by
    have term : ∀ b, f b * graph_idle_measure G α x b = if b = y then 1 - α else 0 := by
      intro b
      rw [hμx]
      by_cases hbx : b = x
      · subst b; simp [hf, hne]
      by_cases hby : b = y
      · subst b; simp [hf, hbx]
      simp [hf, hbx, hby]
    simp_rw [term]
    simp
  have Sy : ∑ b, f b * graph_idle_measure G α y b = α + 2 * q * ((G.degree y : ℝ) - 1) := by
    have term : ∀ b, f b * graph_idle_measure G α y b =
        (if b = y then α else 0) + (if b ∈ (G.neighborFinset y).erase x then 2 * q else 0) := by
      intro b
      rw [hμy]
      by_cases hbx : b = x
      · subst b; simp [hf, hne]
      by_cases hby : b = y
      · subst b; simp [hf, hbx]
      simp [hf, hbx, hby, SimpleGraph.mem_neighborFinset]
    simp_rw [term]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_erase_of_mem (by simpa [SimpleGraph.mem_neighborFinset] using hxy.symm),
      SimpleGraph.card_neighborFinset_eq_degree, Nat.cast_sub (by omega)]
    push_cast; ring
  have hW : graph_wasserstein_dist G (graph_idle_measure G α x) (graph_idle_measure G α y)
      = α + 2 * q * ((G.degree y : ℝ) - 1) - (1 - α) := by
    apply le_antisymm
    · set π : V → V → ℝ := fun a b =>
        (if a = x then graph_idle_measure G α y b - (if b = y then 1 - α else 0) else 0) +
        (if a = y then (if b = y then 1 - α else 0) else 0) with hπ
      have h0 : ∀ a b, 0 ≤ π a b := by
        intro a b
        simp only [hπ]
        have hn := graph_idle_measure_nonneg G α (by linarith) hα2.le y b
        by_cases hax : a = x
        · subst a
          simp only [if_true, if_neg hne, add_zero]
          by_cases hby : b = y
          · subst b; rw [hμy]; simp; linarith
          · simp [hby]; exact hn
        · split_ifs <;> linarith
      have hc : ∀ a b, (G.dist a b : ℝ) * π a b = if a = x then
          (G.dist x b : ℝ) * (graph_idle_measure G α y b - (if b = y then 1 - α else 0)) else 0 := by
        intro a b
        simp only [hπ]
        by_cases hax : a = x
        · subst a; simp [hne]
        · by_cases hay : a = y
          · subst a
            by_cases hby : b = y
            · subst b; simp [hax]
            · simp [hax, hby]
          · simp [hax, hay]
      calc graph_wasserstein_dist G _ _ ≤ ∑ a, ∑ b, (G.dist a b : ℝ) * π a b := by
            apply graph_wasserstein_dist_le_of_plan G _ _ π h0
            · intro a
              simp only [hπ]
              rw [Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_ite_irrel,
                Finset.sum_const_zero, Finset.sum_sub_distrib, hsy]
              simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
              rw [hμx]
              by_cases hax : a = x
              · subst a; simp [hne]
              · by_cases hay : a = y
                · subst a; simp [hax]
                · simp [hax, hay]
            · intro b
              simp only [hπ]
              rw [Finset.sum_add_distrib]
              simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
              ring
        _ = ∑ b, (G.dist x b : ℝ) * graph_idle_measure G α y b - (1 - α) := by
            simp_rw [hc]
            rw [Fintype.sum_eq_single x (fun a ha => by simp [ha])]
            simp only [if_true, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
              Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, hdxy, Nat.cast_one, one_mul]
        _ ≤ ∑ b, f b * graph_idle_measure G α y b - (1 - α) := by
            apply sub_le_sub_right
            apply Finset.sum_le_sum
            intro b _
            rw [hμy]
            split_ifs with h1 h2
            · subst b; simp [hf, hne.symm, hdxy]
            · exact mul_le_mul_of_nonneg_right (hfle b h2) hq0
            · simp
        _ = _ := by rw [Sy]
    · have := graph_wasserstein_dist_ge_of_lipschitz G _ _
        (graph_idle_measure_nonneg G α (by linarith) hα2.le x)
        (graph_idle_measure_nonneg G α (by linarith) hα2.le y) hsx hsy (fun b => -f b) hfge
      simp only [neg_mul, Finset.sum_neg_distrib] at this
      rw [Sx, Sy] at this
      linarith
  unfold graph_ollivier_curvature
  rw [hW, hdxy, hq]
  simp only [Nat.cast_one, div_one]
  field_simp
  ring
