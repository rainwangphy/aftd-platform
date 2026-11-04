import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOrPower
import AFTD.Kb.Tcs.SimpleGraphCategoricalProd
import AFTD.Kb.Tcs.ShannonOrCapacity

/-!
# shannon_or_capacity_categorical_prod_le_min

Topic: information   Node: 5dd197eaae84

Provenance: formalization of a published result. Source: arXiv:2610.41977 Sec. 1

For any finite nonempty simple graphs G and H, the Shannon OR-capacity of their categorical product G × H is at most the minimum of the Shannon OR-capacities of G and H.
-/

lemma shannon_or_capacity_categorical_prod_le_min_cliqueNum_le_card {α : Type*} [Fintype α] (G : SimpleGraph α) :
    G.cliqueNum ≤ Fintype.card α := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  rw [← hs.card_eq]
  exact s.card_le_univ

lemma shannon_or_capacity_categorical_prod_le_min_power_cliqueNum_rpow_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) :
    ((simple_graph_or_power G n).cliqueNum : ℝ) ^ ((1 : ℝ) / n) ≤ (Fintype.card V : ℝ) := by
  have hcard : (simple_graph_or_power G n).cliqueNum ≤ (Fintype.card V) ^ n := by
    have hle := shannon_or_capacity_categorical_prod_le_min_cliqueNum_le_card (simple_graph_or_power G n)
    simp only [Fintype.card_fun, Fintype.card_fin] at hle
    exact hle
  have hcard_r : ((simple_graph_or_power G n).cliqueNum : ℝ) ≤ ((Fintype.card V : ℝ) ^ n) := by
    exact_mod_cast hcard
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_exp_pos : 0 ≤ (1 : ℝ) / n := one_div_nonneg.mpr (le_of_lt hn_pos)
  have h_rpow := Real.rpow_le_rpow (by positivity) hcard_r h_exp_pos
  have h_pow_rpow : (((Fintype.card V : ℝ) ^ n) ^ ((1 : ℝ) / n)) = (Fintype.card V : ℝ) := by
    have h_card_nonneg : 0 ≤ (Fintype.card V : ℝ) := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_card_nonneg]
    have : (n : ℝ) * ((1 : ℝ) / n) = 1 := mul_one_div_cancel (ne_of_gt hn_pos)
    rw [this, Real.rpow_one]
  rwa [h_pow_rpow] at h_rpow

lemma shannon_or_capacity_categorical_prod_le_min_bddAbove_shannon_range
    {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    BddAbove (Set.range (fun n => ⨆ (_ : 1 ≤ n), (((simple_graph_or_power G n).cliqueNum : ℝ) ^ ((1 : ℝ) / n)))) := by
  use (Fintype.card V : ℝ)
  rintro x ⟨n, rfl⟩
  dsimp only
  by_cases hn : 1 ≤ n
  · rw [ciSup_pos hn]
    exact shannon_or_capacity_categorical_prod_le_min_power_cliqueNum_rpow_le G n hn
  · rw [ciSup_neg hn, Real.sSup_empty]
    positivity

theorem shannon_or_capacity_categorical_prod_le_min_cliqueNum_le_fst
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (n : ℕ) :
    (simple_graph_or_power (simple_graph_categorical_prod G H) n).cliqueNum ≤
      (simple_graph_or_power G n).cliqueNum := by
  classical
  obtain ⟨s, hs⟩ := (simple_graph_or_power (simple_graph_categorical_prod G H) n).exists_isNClique_cliqueNum
  rw [SimpleGraph.isNClique_iff] at hs
  rcases hs with ⟨hs_clique, hs_card⟩
  let f : (Fin n → V × W) → (Fin n → V) := fun x => fun i => (x i).1
  have hinj : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    have hadj := hs_clique hx hy hne
    simp only [simple_graph_or_power, simple_graph_categorical_prod] at hadj
    rcases hadj with ⟨i, hiG, _⟩
    have hfi : f x i = f y i := congr_fun hxy i
    dsimp [f] at hfi
    exact G.ne_of_adj hiG hfi
  have hcard : s.card = (s.image f).card := by
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    exact hinj x hx y hy hxy
  have hclique : (simple_graph_or_power G n).IsClique (s.image f : Set (Fin n → V)) := by
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_image] at hu hv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    have hne : x ≠ y := by
      rintro rfl
      exact huv rfl
    have hadj := hs_clique hx hy hne
    simp only [simple_graph_or_power, simple_graph_categorical_prod] at hadj
    rcases hadj with ⟨i, hiG, _⟩
    exact ⟨i, hiG⟩
  have hle := SimpleGraph.IsClique.card_le_cliqueNum (tc := hclique)
  rw [← hs_card, hcard]
  exact hle

theorem shannon_or_capacity_categorical_prod_le_min_cliqueNum_le_snd
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (n : ℕ) :
    (simple_graph_or_power (simple_graph_categorical_prod G H) n).cliqueNum ≤
      (simple_graph_or_power H n).cliqueNum := by
  classical
  obtain ⟨s, hs⟩ := (simple_graph_or_power (simple_graph_categorical_prod G H) n).exists_isNClique_cliqueNum
  rw [SimpleGraph.isNClique_iff] at hs
  rcases hs with ⟨hs_clique, hs_card⟩
  let f : (Fin n → V × W) → (Fin n → W) := fun x => fun i => (x i).2
  have hinj : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y := by
    intro x hx y hy hxy
    by_contra hne
    have hadj := hs_clique hx hy hne
    simp only [simple_graph_or_power, simple_graph_categorical_prod] at hadj
    rcases hadj with ⟨i, _, hiH⟩
    have hfi : f x i = f y i := congr_fun hxy i
    dsimp [f] at hfi
    exact H.ne_of_adj hiH hfi
  have hcard : s.card = (s.image f).card := by
    rw [Finset.card_image_of_injOn]
    intro x hx y hy hxy
    exact hinj x hx y hy hxy
  have hclique : (simple_graph_or_power H n).IsClique (s.image f : Set (Fin n → W)) := by
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_image] at hu hv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    have hne : x ≠ y := by
      rintro rfl
      exact huv rfl
    have hadj := hs_clique hx hy hne
    simp only [simple_graph_or_power, simple_graph_categorical_prod] at hadj
    rcases hadj with ⟨i, _, hiH⟩
    exact ⟨i, hiH⟩
  have hle := SimpleGraph.IsClique.card_le_cliqueNum (tc := hclique)
  rw [← hs_card, hcard]
  exact hle

theorem shannon_or_capacity_categorical_prod_le_min_le_fst
    {V W : Type*} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    shannon_or_capacity (simple_graph_categorical_prod G H) ≤ shannon_or_capacity G := by
  dsimp only [shannon_or_capacity]
  apply ciSup_le
  intro n
  by_cases hn : 1 ≤ n
  · rw [ciSup_pos hn]
    have hclique := shannon_or_capacity_categorical_prod_le_min_cliqueNum_le_fst G H n
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have h_exp_pos : 0 ≤ (1 : ℝ) / n := one_div_nonneg.mpr (le_of_lt hn_pos)
    have h_rpow : ((simple_graph_or_power (simple_graph_categorical_prod G H) n).cliqueNum : ℝ) ^ ((1 : ℝ) / n) ≤
        ((simple_graph_or_power G n).cliqueNum : ℝ) ^ ((1 : ℝ) / n) := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hclique) h_exp_pos
    have h_le_sup := le_ciSup (shannon_or_capacity_categorical_prod_le_min_bddAbove_shannon_range G) n
    rw [ciSup_pos hn] at h_le_sup
    exact h_rpow.trans h_le_sup
  · rw [ciSup_neg hn, Real.sSup_empty]
    have h1 : 1 ≤ 1 := le_refl 1
    have h_pos : 0 ≤ ((simple_graph_or_power G 1).cliqueNum : ℝ) ^ ((1 : ℝ) / ↑(1 : ℕ)) := by positivity
    have h_le_sup := le_ciSup (shannon_or_capacity_categorical_prod_le_min_bddAbove_shannon_range G) 1
    rw [ciSup_pos h1] at h_le_sup
    exact h_pos.trans h_le_sup

theorem shannon_or_capacity_categorical_prod_le_min_le_snd
    {V W : Type*} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    shannon_or_capacity (simple_graph_categorical_prod G H) ≤ shannon_or_capacity H := by
  dsimp only [shannon_or_capacity]
  apply ciSup_le
  intro n
  by_cases hn : 1 ≤ n
  · rw [ciSup_pos hn]
    have hclique := shannon_or_capacity_categorical_prod_le_min_cliqueNum_le_snd G H n
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have h_exp_pos : 0 ≤ (1 : ℝ) / n := one_div_nonneg.mpr (le_of_lt hn_pos)
    have h_rpow : ((simple_graph_or_power (simple_graph_categorical_prod G H) n).cliqueNum : ℝ) ^ ((1 : ℝ) / n) ≤
        ((simple_graph_or_power H n).cliqueNum : ℝ) ^ ((1 : ℝ) / n) := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hclique) h_exp_pos
    have h_le_sup := le_ciSup (shannon_or_capacity_categorical_prod_le_min_bddAbove_shannon_range H) n
    rw [ciSup_pos hn] at h_le_sup
    exact h_rpow.trans h_le_sup
  · rw [ciSup_neg hn, Real.sSup_empty]
    have h1 : 1 ≤ 1 := le_refl 1
    have h_pos : 0 ≤ ((simple_graph_or_power H 1).cliqueNum : ℝ) ^ ((1 : ℝ) / ↑(1 : ℕ)) := by positivity
    have h_le_sup := le_ciSup (shannon_or_capacity_categorical_prod_le_min_bddAbove_shannon_range H) 1
    rw [ciSup_pos h1] at h_le_sup
    exact h_pos.trans h_le_sup

/-- The Shannon OR-capacity of a categorical product is at most the minimum of the factor capacities. -/
theorem shannon_or_capacity_categorical_prod_le_min {V W : Type*} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W] (G : SimpleGraph V) (H : SimpleGraph W) : shannon_or_capacity (simple_graph_categorical_prod G H) ≤ min (shannon_or_capacity G) (shannon_or_capacity H) := le_min (shannon_or_capacity_categorical_prod_le_min_le_fst G H)
          (shannon_or_capacity_categorical_prod_le_min_le_snd G H)
