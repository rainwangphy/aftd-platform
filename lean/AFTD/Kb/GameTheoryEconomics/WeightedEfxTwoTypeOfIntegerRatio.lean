import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsWefxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# weighted_efx_two_type_of_integer_ratio

Topic: fair_division   Node: e7d8d408a2db

Provenance: formalization of a published result. Source: arXiv:2305.16081, Thm. 10

For two agents with positive entitlements whose ratio max(w_0, w_1) / min(w_0, w_1) is a positive integer, every instance with two types of indivisible goods and strictly positive additive valuations admits a complete weighted-EFX allocation.
-/

def weighted_efx_two_type_of_integer_ratio_sum_sq_val {m K : ℕ} (u : Fin m → ℝ) (σ : Fin m → Fin K) : ℝ :=
  ∑ r : Fin K, (additive_valuation u (bundle_of σ r)) ^ 2

lemma weighted_efx_two_type_of_integer_ratio_bundle_of_update {m K : ℕ} (σ : Fin m → Fin K) (g : Fin m) (j : Fin K) (r : Fin K) :
    bundle_of (Function.update σ g j) r =
      if r = j then insert g (bundle_of σ r)
      else (bundle_of σ r).erase g := by
  ext x
  dsimp [bundle_of]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with hr
  · subst hr
    simp only [Finset.mem_insert]
    by_cases hx : x = g
    · subst hx
      simp
    · rw [Function.update_of_ne hx]
      simp [hx]
  · simp only [Finset.mem_erase]
    by_cases hx : x = g
    · subst hx
      rw [Function.update_self]
      simp [ne_comm.mp hr]
    · rw [Function.update_of_ne hx]
      simp [hx]

lemma weighted_efx_two_type_of_integer_ratio_sum_pair_split {K : ℕ} (i j : Fin K) (hij : i ≠ j) (f g : Fin K → ℝ)
    (h_rest : ∀ r, r ≠ i → r ≠ j → f r = g r) :
    ∑ r, f r - ∑ r, g r = (f i + f j) - (g i + g j) := by
  have h_split (h : Fin K → ℝ) :
      ∑ r, h r = h i + h j + ∑ r ∈ (Finset.univ.erase i).erase j, h r := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hj_mem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]; exact ⟨Ne.symm hij, Finset.mem_univ j⟩
    rw [← Finset.add_sum_erase _ _ hj_mem]; ring
  rw [h_split f, h_split g]
  have h_eq : ∑ r ∈ (Finset.univ.erase i).erase j, f r = ∑ r ∈ (Finset.univ.erase i).erase j, g r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_erase, Finset.mem_erase] at hr
    exact h_rest r hr.2.1 hr.1
  rw [h_eq]; ring

lemma weighted_efx_two_type_of_integer_ratio_additive_valuation_erase {m : ℕ} (u : Fin m → ℝ) (s : Finset (Fin m)) (g : Fin m) (hg : g ∈ s) :
    additive_valuation u (s.erase g) = additive_valuation u s - u g := by
  simp [additive_valuation, ← Finset.sum_erase_add _ _ hg]

lemma weighted_efx_two_type_of_integer_ratio_additive_valuation_insert {m : ℕ} (u : Fin m → ℝ) (s : Finset (Fin m)) (g : Fin m) (hg : g ∉ s) :
    additive_valuation u (insert g s) = additive_valuation u s + u g := by
  simp [additive_valuation, Finset.sum_insert hg, add_comm]

lemma weighted_efx_two_type_of_integer_ratio_min_sum_sq_efx {m K : ℕ} (u : Fin m → ℝ) (hu : ∀ g, 0 < u g)
    (σ : Fin m → Fin K) (hσ : ∀ τ : Fin m → Fin K, weighted_efx_two_type_of_integer_ratio_sum_sq_val u σ ≤ weighted_efx_two_type_of_integer_ratio_sum_sq_val u τ)
    (i j : Fin K) (hij : i ≠ j) (g : Fin m) (hg : g ∈ bundle_of σ i) :
    additive_valuation u ((bundle_of σ i).erase g) ≤ additive_valuation u (bundle_of σ j) := by
  have h_min := hσ (Function.update σ g j)
  have hg_eq : σ g = i := by
    rw [bundle_of, Finset.mem_filter] at hg; exact hg.2
  have hg_not_j : g ∉ bundle_of σ j := by
    rw [bundle_of, Finset.mem_filter]; rintro ⟨-, h⟩; subst hg_eq; subst h; exact hij rfl
  have h_diff : 0 ≤ weighted_efx_two_type_of_integer_ratio_sum_sq_val u (Function.update σ g j) - weighted_efx_two_type_of_integer_ratio_sum_sq_val u σ :=
    sub_nonneg.mpr h_min
  have h_rest : ∀ r, r ≠ i → r ≠ j →
      (additive_valuation u (bundle_of (Function.update σ g j) r)) ^ 2 =
      (additive_valuation u (bundle_of σ r)) ^ 2 := by
    intro r hri hrj; congr 2; rw [weighted_efx_two_type_of_integer_ratio_bundle_of_update]
    split_ifs with hr
    · subst hr; contradiction
    · apply Finset.erase_eq_of_notMem
      intro h_mem; rw [bundle_of, Finset.mem_filter] at h_mem
      exact hri (hg_eq.symm.trans h_mem.2).symm
  have h_split := weighted_efx_two_type_of_integer_ratio_sum_pair_split i j hij _ _ h_rest
  dsimp [weighted_efx_two_type_of_integer_ratio_sum_sq_val] at h_diff
  rw [h_split] at h_diff
  have hb_i : bundle_of (Function.update σ g j) i = (bundle_of σ i).erase g := by
    rw [weighted_efx_two_type_of_integer_ratio_bundle_of_update, if_neg hij]
  have hb_j : bundle_of (Function.update σ g j) j = insert g (bundle_of σ j) := by
    rw [weighted_efx_two_type_of_integer_ratio_bundle_of_update, if_pos rfl]
  rw [hb_i, hb_j] at h_diff
  rw [weighted_efx_two_type_of_integer_ratio_additive_valuation_erase u _ g hg] at h_diff
  rw [weighted_efx_two_type_of_integer_ratio_additive_valuation_insert u _ g hg_not_j] at h_diff
  have hug := hu g
  set X := additive_valuation u (bundle_of σ i)
  set Y := additive_valuation u (bundle_of σ j)
  set d := u g
  have h_alg : X - d ≤ Y := by nlinarith
  rw [weighted_efx_two_type_of_integer_ratio_additive_valuation_erase u _ g hg]
  exact h_alg

lemma weighted_efx_two_type_of_integer_ratio_additive_valuation_compl {m K : ℕ} (u : Fin m → ℝ) (σ : Fin m → Fin K) (i_star : Fin K) :
    additive_valuation u ((bundle_of σ i_star)ᶜ) =
      ∑ r ∈ Finset.univ.erase i_star, additive_valuation u (bundle_of σ r) := by
  dsimp [additive_valuation]
  have h_biUnion : (bundle_of σ i_star)ᶜ =
      (Finset.univ.erase i_star).biUnion (fun r => bundle_of σ r) := by
    ext g
    simp only [Finset.mem_compl, bundle_of, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · intro h
      exact ⟨σ g, ⟨h, trivial⟩, rfl⟩
    · rintro ⟨r, ⟨hr, -⟩, rfl⟩
      exact hr
  rw [h_biUnion]
  have h_disj : (∀ x ∈ Finset.univ.erase i_star, ∀ y ∈ Finset.univ.erase i_star,
      x ≠ y → Disjoint (bundle_of σ x) (bundle_of σ y)) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro g hx hy
    rw [bundle_of, Finset.mem_filter] at hx hy
    exact hxy (hx.2.symm.trans hy.2)
  rw [Finset.sum_biUnion h_disj]

lemma weighted_efx_two_type_of_integer_ratio_agent_L {m k : ℕ} (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g)
    (σ : Fin m → Fin (k + 1)) (i_star : Fin (k + 1))
    (h_max : ∀ r, additive_valuation u (bundle_of σ r) ≤ additive_valuation u (bundle_of σ i_star))
    (wL wH : ℝ) (hwL : 0 < wL) (hk : 0 < k) (hwH : wH = (k : ℝ) * wL)
    (g : Fin m) (_hg : g ∈ (bundle_of σ i_star)ᶜ) :
    additive_valuation u (((bundle_of σ i_star)ᶜ).erase g) / wH ≤
      additive_valuation u (bundle_of σ i_star) / wL := by
  have h_le : additive_valuation u (((bundle_of σ i_star)ᶜ).erase g) ≤
      additive_valuation u ((bundle_of σ i_star)ᶜ) := by
    dsimp [additive_valuation]; apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.erase_subset g _
    · intro x _ _; exact hu x
  rw [weighted_efx_two_type_of_integer_ratio_additive_valuation_compl u σ i_star] at h_le
  have h_card : (Finset.univ.erase i_star : Finset (Fin (k + 1))).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i_star), Finset.card_univ, Fintype.card_fin]
    exact Nat.succ_sub_one k
  have h_sum_le : ∑ r ∈ Finset.univ.erase i_star, additive_valuation u (bundle_of σ r) ≤
      (k : ℝ) * additive_valuation u (bundle_of σ i_star) := by
    have := Finset.sum_le_card_nsmul (Finset.univ.erase i_star) _ _ (fun r _ => h_max r)
    rw [h_card, nsmul_eq_mul] at this; exact this
  have h_trans := h_le.trans h_sum_le
  rw [hwH]
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have h_cancel : ((k : ℝ) * additive_valuation u (bundle_of σ i_star)) / ((k : ℝ) * wL) =
      additive_valuation u (bundle_of σ i_star) / wL := by
    rw [mul_div_mul_left _ _ (ne_of_gt hk_pos)]
  rw [← h_cancel]
  exact div_le_div_of_nonneg_right h_trans (by positivity)

lemma weighted_efx_two_type_of_integer_ratio_agent_H {m k : ℕ} (u : Fin m → ℝ)
    (σ : Fin m → Fin (k + 1)) (i_star : Fin (k + 1))
    (h_efx : ∀ r, r ≠ i_star → ∀ g ∈ bundle_of σ i_star,
      additive_valuation u ((bundle_of σ i_star).erase g) ≤ additive_valuation u (bundle_of σ r))
    (wL wH : ℝ) (hwL : 0 < wL) (hk : 0 < k) (hwH : wH = (k : ℝ) * wL)
    (g : Fin m) (hg : g ∈ bundle_of σ i_star) :
    additive_valuation u ((bundle_of σ i_star).erase g) / wL ≤
      additive_valuation u ((bundle_of σ i_star)ᶜ) / wH := by
  have h_compl := weighted_efx_two_type_of_integer_ratio_additive_valuation_compl u σ i_star
  rw [h_compl]
  have h_card : (Finset.univ.erase i_star : Finset (Fin (k + 1))).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i_star), Finset.card_univ, Fintype.card_fin]
    exact Nat.succ_sub_one k
  have h_le_sum : (k : ℝ) * additive_valuation u ((bundle_of σ i_star).erase g) ≤
      ∑ r ∈ Finset.univ.erase i_star, additive_valuation u (bundle_of σ r) := by
    have := Finset.card_nsmul_le_sum (Finset.univ.erase i_star)
      (fun r => additive_valuation u (bundle_of σ r))
      (additive_valuation u ((bundle_of σ i_star).erase g))
      (fun r hr => h_efx r (Finset.mem_erase.mp hr).1 g hg)
    rw [h_card, nsmul_eq_mul] at this; exact this
  rw [hwH]
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have h_cancel : ((k : ℝ) * additive_valuation u ((bundle_of σ i_star).erase g)) / ((k : ℝ) * wL) =
      additive_valuation u ((bundle_of σ i_star).erase g) / wL := by
    rw [mul_div_mul_left _ _ (ne_of_gt hk_pos)]
  rw [← h_cancel]
  exact div_le_div_of_nonneg_right h_le_sum (by positivity)

lemma weighted_efx_two_type_of_integer_ratio_final_bundles {m K : ℕ} (L H : Fin 2) (hLH : L ≠ H)
    (σ_min : Fin m → Fin K) (i_star : Fin K) :
    let σ_final : Fin m → Fin 2 := fun g => if σ_min g = i_star then L else H
    bundle_of σ_final L = bundle_of σ_min i_star ∧
    bundle_of σ_final H = (bundle_of σ_min i_star)ᶜ := by
  intro σ_final
  constructor
  · ext x
    simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [σ_final]
    split_ifs with h
    · simp [h]
    · simp [h, hLH.symm]
  · ext x
    simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    dsimp [σ_final]
    split_ifs with h
    · simp [h, hLH]
    · simp [h]

lemma weighted_efx_two_type_of_integer_ratio_fin2_cases_distinct (L H i j : Fin 2) (hLH : L ≠ H) (hij : i ≠ j) :
    (i = L ∧ j = H) ∨ (i = H ∧ j = L) := by
  revert i j L H
  decide

lemma weighted_efx_two_type_of_integer_ratio_two_type_aux (w : Fin 2 → ℝ) (hw : ∀ i, 0 < w i) (L H : Fin 2) (hLH : L ≠ H)
    (k : ℕ) (hk : 0 < k) (hwH : w H = (k : ℝ) * w L) (m : ℕ) (u : Fin 2 → Fin m → ℝ)
    (hu_pos : ∀ i g, 0 < u i g) :
    ∃ σ : Fin m → Fin 2, is_wefx_goods w u σ := by
  have ⟨σ_min, hσ_min⟩ := Finite.exists_min (fun σ : Fin m → Fin (k + 1) => weighted_efx_two_type_of_integer_ratio_sum_sq_val (u H) σ)
  have ⟨i_star, hi_star⟩ := Finite.exists_max (fun r : Fin (k + 1) => additive_valuation (u L) (bundle_of σ_min r))
  let σ_final : Fin m → Fin 2 := fun g => if σ_min g = i_star then L else H
  use σ_final
  have h_bundles := weighted_efx_two_type_of_integer_ratio_final_bundles L H hLH σ_min i_star
  dsimp [σ_final] at h_bundles
  have hbL := h_bundles.1
  have hbH := h_bundles.2
  intro i j hij
  have h_cases := weighted_efx_two_type_of_integer_ratio_fin2_cases_distinct L H i j hLH hij
  rcases h_cases with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [hi, hj]
    intro g hg
    rw [hbL, hbH]
    rw [hbH] at hg
    exact weighted_efx_two_type_of_integer_ratio_agent_L (u L) (fun x => (hu_pos L x).le) σ_min i_star hi_star (w L) (w H) (hw L) hk hwH g hg
  · rw [hi, hj]
    intro g hg
    rw [hbL, hbH]
    rw [hbL] at hg
    have h_efx : ∀ r, r ≠ i_star → ∀ g' ∈ bundle_of σ_min i_star,
        additive_valuation (u H) ((bundle_of σ_min i_star).erase g') ≤ additive_valuation (u H) (bundle_of σ_min r) := by
      intro r hr g' hg'
      exact weighted_efx_two_type_of_integer_ratio_min_sum_sq_efx (u H) (hu_pos H) σ_min hσ_min i_star r hr.symm g' hg'
    exact weighted_efx_two_type_of_integer_ratio_agent_H (u H) σ_min i_star h_efx (w L) (w H) (hw L) hk hwH g hg

/-- Positive integer entitlement ratios guarantee the existence of a complete weighted-EFX allocation for two-type goods. -/
theorem weighted_efx_two_type_of_integer_ratio (w : Fin 2 → ℝ) (hw : ∀ i, 0 < w i)
    (h_int : ∃ k : ℕ, 0 < k ∧ max (w 0) (w 1) / min (w 0) (w 1) = (k : ℝ)) :
    ∀ (m : ℕ) (τ : Fin m → Fin 2) (v : Fin 2 → Fin 2 → ℝ),
      (∀ i t, 0 < v i t) →
      ∃ σ : Fin m → Fin 2, is_wefx_goods w (fun i g => v i (τ g)) σ := by
  intro m τ v hv
  rcases h_int with ⟨k, hk, h_ratio⟩
  have hu_pos : ∀ i g, 0 < (fun i g => v i (τ g)) i g := fun i g => hv i (τ g)
  rcases le_total (w 0) (w 1) with hle | hle
  · rw [max_eq_right hle, min_eq_left hle] at h_ratio
    have hw1 : w 1 = (k : ℝ) * w 0 := by
      rw [← h_ratio, div_mul_cancel₀ _ (ne_of_gt (hw 0))]
    exact weighted_efx_two_type_of_integer_ratio_two_type_aux w hw 0 1 (by decide) k hk hw1 m (fun i g => v i (τ g)) hu_pos
  · rw [max_eq_left hle, min_eq_right hle] at h_ratio
    have hw0 : w 0 = (k : ℝ) * w 1 := by
      rw [← h_ratio, div_mul_cancel₀ _ (ne_of_gt (hw 1))]
    exact weighted_efx_two_type_of_integer_ratio_two_type_aux w hw 1 0 (by decide) k hk hw0 m (fun i g => v i (τ g)) hu_pos
