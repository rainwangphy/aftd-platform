import AFTD.Prelude
import AFTD.Kb.Tcs.ShannonOrCapacityCategoricalProdLeMin
import AFTD.Kb.Tcs.ShannonOrCapacity
import AFTD.Kb.Tcs.SimpleGraphCategoricalProd
import AFTD.Kb.Tcs.SimpleGraphOrPower

/-!
# shannon_or_capacity_categorical_prod_of_min_eq_two

Topic: information   Node: dcf7d2be2798

Provenance: formalization of a published result. Source: arXiv:2610.41977 Sec. 6

For any finite nonempty simple graphs G and H, if the minimum of their Shannon OR-capacities is 2, then the Shannon OR-capacity of their categorical product G × H is 2.
-/

private lemma shannon_or_capacity_categorical_prod_of_min_eq_two_cliqueNum_le_one
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : ∀ u v : V, ¬ G.Adj u v) : G.cliqueNum ≤ 1 := by
  obtain ⟨s, hs, hcard⟩ := G.exists_isNClique_cliqueNum
  rw [← hcard]
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  exact h a b (hs ha hb hab)

private lemma shannon_or_capacity_categorical_prod_of_min_eq_two_le_one_of_no_adj
    {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (h : ∀ u v : V, ¬ G.Adj u v) : shannon_or_capacity G ≤ 1 := by
  unfold shannon_or_capacity
  apply ciSup_le
  intro n
  by_cases hn : 1 ≤ n
  · rw [ciSup_pos hn]
    have hno : ∀ x y : Fin n → V, ¬ (simple_graph_or_power G n).Adj x y := by
      intro x y hxy
      obtain ⟨i, hi⟩ := hxy
      exact h (x i) (y i) hi
    have hcl : (simple_graph_or_power G n).cliqueNum ≤ 1 :=
      shannon_or_capacity_categorical_prod_of_min_eq_two_cliqueNum_le_one _ hno
    have hclr : ((simple_graph_or_power G n).cliqueNum : ℝ) ≤ 1 := by exact_mod_cast hcl
    exact Real.rpow_le_one (by positivity) hclr (by positivity)
  · simp [hn]

private lemma shannon_or_capacity_categorical_prod_of_min_eq_two_two_le_of_adj
    {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) {u v : V} (h : G.Adj u v) :
    2 ≤ shannon_or_capacity G := by
  classical
  have hcl : 2 ≤ (simple_graph_or_power G 1).cliqueNum := by
    have hc : (simple_graph_or_power G 1).IsClique
        ({(fun _ : Fin 1 => u), (fun _ : Fin 1 => v)} : Finset (Fin 1 → V)) := by
      intro a ha b hb hab
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact ⟨0, h⟩
      · exact ⟨0, (G.adj_comm v u).mpr h⟩
      · exact absurd rfl hab
    have hcard : ({(fun _ : Fin 1 => u), (fun _ : Fin 1 => v)} : Finset (Fin 1 → V)).card = 2 := by
      rw [Finset.card_pair]
      intro heq
      exact G.ne_of_adj h (congrFun heq 0)
    have := hc.card_le_cliqueNum
    rwa [hcard] at this
  unfold shannon_or_capacity
  have hclr : (2:ℝ) ≤ ((simple_graph_or_power G 1).cliqueNum : ℝ) := by exact_mod_cast hcl
  have hterm : (2:ℝ) ≤ ⨆ (_ : 1 ≤ (1:ℕ)), ((simple_graph_or_power G 1).cliqueNum : ℝ) ^ ((1:ℝ)/↑(1:ℕ)) := by
    rw [ciSup_pos (le_refl 1)]
    rw [show (1:ℝ)/↑(1:ℕ) = 1 by norm_num, Real.rpow_one]
    exact hclr
  have hbdd := shannon_or_capacity_categorical_prod_le_min_bddAbove_shannon_range G
  exact le_trans hterm (le_ciSup hbdd 1)

/-- Hedetniemi's identity for Shannon OR-capacity holds when the smaller factor capacity is two. -/
theorem shannon_or_capacity_categorical_prod_of_min_eq_two {V W : Type*} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W] (G : SimpleGraph V) (H : SimpleGraph W) (h : min (shannon_or_capacity G) (shannon_or_capacity H) = 2) : shannon_or_capacity (simple_graph_categorical_prod G H) = 2 := by
  have hG : 2 ≤ shannon_or_capacity G := by rw [← h]; exact min_le_left _ _
  have hH : 2 ≤ shannon_or_capacity H := by rw [← h]; exact min_le_right _ _
  have hedgeG : ∃ u v : V, G.Adj u v := by
    by_contra hne
    push Not at hne
    have hle := shannon_or_capacity_categorical_prod_of_min_eq_two_le_one_of_no_adj G hne
    linarith
  obtain ⟨u, v, huv⟩ := hedgeG
  have hedgeH : ∃ x y : W, H.Adj x y := by
    by_contra hne
    push Not at hne
    have hle := shannon_or_capacity_categorical_prod_of_min_eq_two_le_one_of_no_adj H hne
    linarith
  obtain ⟨x, y, hxy⟩ := hedgeH
  have hadj : (simple_graph_categorical_prod G H).Adj (u, x) (v, y) := ⟨huv, hxy⟩
  have hlower : 2 ≤ shannon_or_capacity (simple_graph_categorical_prod G H) :=
    shannon_or_capacity_categorical_prod_of_min_eq_two_two_le_of_adj _ hadj
  have hupper : shannon_or_capacity (simple_graph_categorical_prod G H) ≤ 2 := by
    have hle := shannon_or_capacity_categorical_prod_le_min G H
    rw [h] at hle
    exact hle
  linarith
