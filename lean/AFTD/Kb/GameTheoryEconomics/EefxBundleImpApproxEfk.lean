import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleRemoveKValue
import AFTD.Kb.GameTheoryEconomics.BundleRemoveKValueLe
import AFTD.Kb.GameTheoryEconomics.IsAlphaEefxBundle
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.Tcs.G

/-!
# eefx_bundle_imp_approx_efk

Topic: fair_division   Node: 02271419cda2

Provenance: helper lemma. arXiv:2610.34625, Lemma 3.2

Let n ≥ 3 and let σ be an allocation of m goods among n agents with nonnegative additive valuations u such that every agent's bundle is nonempty. If agent i's bundle is EEFX for agent i, then for every agent j ≠ i, agent i's valuation of her bundle is at least 1/(n-1) times the value of agent j's bundle after removing the n-2 most valuable goods for agent i.
-/

open Finset

noncomputable def eefx_bundle_imp_approx_efk_pick_one {α : Type*} (s : Finset α) : Finset α :=
  if h : s.Nonempty then {Classical.choose h} else ∅

lemma eefx_bundle_imp_approx_efk_pick_one_card_le {α : Type*} (s : Finset α) :
    (eefx_bundle_imp_approx_efk_pick_one s).card ≤ 1 := by
  unfold eefx_bundle_imp_approx_efk_pick_one
  split_ifs
  · simp
  · simp

lemma eefx_bundle_imp_approx_efk_pick_one_subset {α : Type*} (s : Finset α) :
    eefx_bundle_imp_approx_efk_pick_one s ⊆ s := by
  unfold eefx_bundle_imp_approx_efk_pick_one
  split_ifs with h
  · intro x hx
    simp only [mem_singleton] at hx
    subst hx
    exact Classical.choose_spec h
  · exact empty_subset _

lemma eefx_bundle_imp_approx_efk_val_empty {m : ℕ} (u : Fin m → ℝ) :
    additive_valuation u ∅ = 0 := by
  unfold additive_valuation
  simp

lemma eefx_bundle_imp_approx_efk_val_mono {m : ℕ} (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g)
    {S T : Finset (Fin m)} (h : S ⊆ T) :
    additive_valuation u S ≤ additive_valuation u T := by
  unfold additive_valuation
  exact sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hu i)

lemma eefx_bundle_imp_approx_efk_val_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g)
    (S : Finset (Fin m)) :
    0 ≤ additive_valuation u S := by
  unfold additive_valuation
  exact sum_nonneg (fun i _ => hu i)

lemma eefx_bundle_imp_approx_efk_sum_val_partition {m n : ℕ} (u : Fin m → ℝ)
    (A : Finset (Fin m)) (Y : Fin (n - 1) → Finset (Fin m))
    (hY_disj : ∀ p q : Fin (n - 1), p ≠ q → Disjoint (Y p) (Y q))
    (hA : A ⊆ Finset.univ.biUnion Y) :
    additive_valuation u A = ∑ p : Fin (n - 1), additive_valuation u (A ∩ Y p) := by
  have h_eq : univ.biUnion (fun p => A ∩ Y p) = A := by
    ext x
    simp only [mem_biUnion, mem_inter, mem_univ, true_and]
    constructor
    · rintro ⟨p, hxA, -⟩
      exact hxA
    · intro hxA
      have hx : x ∈ univ.biUnion Y := hA hxA
      rw [mem_biUnion] at hx
      rcases hx with ⟨p, -, hxY⟩
      exact ⟨p, hxA, hxY⟩
  have h_pw : (↑(univ : Finset (Fin (n - 1))) : Set (Fin (n - 1))).PairwiseDisjoint (fun p => A ∩ Y p) := by
    intro p _ q _ hpq
    exact Disjoint.mono inter_subset_right inter_subset_right (hY_disj p q hpq)
  unfold additive_valuation
  nth_rw 1 [← h_eq]
  exact sum_biUnion h_pw

lemma eefx_bundle_imp_approx_efk_part_val_le {m n : ℕ}
    (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g)
    (A_i A_j : Finset (Fin m))
    (Y : Fin (n - 1) → Finset (Fin m))
    (hY_bound : ∀ p : Fin (n - 1), ∀ g ∈ Y p, 1 * additive_valuation u ((Y p).erase g) ≤ additive_valuation u A_i)
    (P_sub : Finset (Fin (n - 1)))
    (hP_sub : ∀ p, p ∈ P_sub ↔ Y p ⊆ A_j)
    (X : Finset (Fin m))
    (hX : X = P_sub.biUnion (fun p => eefx_bundle_imp_approx_efk_pick_one (Y p)))
    (p : Fin (n - 1)) :
    additive_valuation u ((A_j \ X) ∩ Y p) ≤ additive_valuation u A_i := by
  by_cases hp : p ∈ P_sub
  · by_cases hne : (Y p).Nonempty
    · obtain ⟨g, hg_in, hg_pick⟩ : ∃ g ∈ Y p, eefx_bundle_imp_approx_efk_pick_one (Y p) = {g} := by
        unfold eefx_bundle_imp_approx_efk_pick_one
        simp only [hne, dite_true]
        exact ⟨Classical.choose hne, Classical.choose_spec hne, rfl⟩
      have hg_in_X : g ∈ X := by
        rw [hX, mem_biUnion]
        exact ⟨p, hp, by rw [hg_pick]; exact mem_singleton_self g⟩
      have h_sub : (A_j \ X) ∩ Y p ⊆ (Y p).erase g := by
        intro x hx
        simp only [mem_inter, mem_sdiff] at hx
        rw [mem_erase]
        refine ⟨?_, hx.2⟩
        rintro rfl
        exact hx.1.2 hg_in_X
      have h_mono := eefx_bundle_imp_approx_efk_val_mono u hu h_sub
      have h_bound := hY_bound p g hg_in
      rw [one_mul] at h_bound
      exact h_mono.trans h_bound
    · have hY_empty : Y p = ∅ := not_nonempty_iff_eq_empty.mp hne
      have h_inter_empty : (A_j \ X) ∩ Y p = ∅ := by rw [hY_empty, inter_empty]
      rw [h_inter_empty, eefx_bundle_imp_approx_efk_val_empty]
      exact eefx_bundle_imp_approx_efk_val_nonneg u hu A_i
  · rw [hP_sub] at hp
    have ⟨g, hg_in, hg_not_Aj⟩ : ∃ g ∈ Y p, g ∉ A_j := by
      by_contra! hc
      exact hp hc
    have h_sub : (A_j \ X) ∩ Y p ⊆ (Y p).erase g := by
      intro x hx
      simp only [mem_inter, mem_sdiff] at hx
      rw [mem_erase]
      refine ⟨?_, hx.2⟩
      rintro rfl
      exact hg_not_Aj hx.1.1
    have h_mono := eefx_bundle_imp_approx_efk_val_mono u hu h_sub
    have h_bound := hY_bound p g hg_in
    rw [one_mul] at h_bound
    exact h_mono.trans h_bound

/-- If an allocation among n ≥ 3 agents has only nonempty bundles and agent i's bundle is EEFX, then i's value for her bundle is at least 1/(n-1) times the value of any other bundle after removing n-2 goods. -/
theorem eefx_bundle_imp_approx_efk {m n : ℕ} (hn : 3 ≤ n)
    (u : Fin n → Fin m → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (σ : Fin m → Fin n) (h_nonempty : ∀ k : Fin n, (bundle_of σ k).Nonempty)
    (i j : Fin n) (hij : i ≠ j)
    (h_eefx : is_alpha_eefx_bundle (additive_valuation (u i)) n 1 (bundle_of σ i)) :
    (1 / ((n : ℝ) - 1)) * bundle_remove_k_value (additive_valuation (u i)) (n - 2) (bundle_of σ j) ≤
      additive_valuation (u i) (bundle_of σ i) := by
  rcases h_eefx with ⟨Y, hY_disj, hY_union, hY_bound⟩
  have ⟨k, hki, hkj⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
    have h_card : ({i, j} : Finset (Fin n)).card = 2 := card_pair hij
    have : ∃ k : Fin n, k ∉ ({i, j} : Finset (Fin n)) := by
      by_contra! hc
      have heq : ({i, j} : Finset (Fin n)) = univ := by
        ext x; simp [hc x]
      have hlen := congr_arg Finset.card heq
      rw [h_card, card_univ, Fintype.card_fin] at hlen
      omega
    rcases this with ⟨k, hk⟩
    simp only [mem_insert, mem_singleton, not_or] at hk
    exact ⟨k, hk.1, hk.2⟩
  obtain ⟨g0, hg0⟩ := h_nonempty k
  have hg0_σ : σ g0 = k := by
    unfold bundle_of at hg0
    simp only [mem_filter, mem_univ, true_and] at hg0
    exact hg0
  have hg0_not_i : g0 ∉ bundle_of σ i := by
    unfold bundle_of
    simp only [mem_filter, mem_univ, true_and]
    intro h
    exact hki (hg0_σ.symm.trans h)
  have hg0_not_j : g0 ∉ bundle_of σ j := by
    unfold bundle_of
    simp only [mem_filter, mem_univ, true_and]
    intro h
    exact hkj (hg0_σ.symm.trans h)
  have hg0_in_diff : g0 ∈ Finset.univ \ bundle_of σ i := by
    rw [mem_sdiff]
    exact ⟨mem_univ _, hg0_not_i⟩
  rw [← hY_union, mem_biUnion] at hg0_in_diff
  rcases hg0_in_diff with ⟨p0, -, hg0_in_Y⟩
  have hp0_not_sub : ¬ (Y p0 ⊆ bundle_of σ j) := by
    intro hsub
    exact hg0_not_j (hsub hg0_in_Y)
  set P_sub : Finset (Fin (n - 1)) := univ.filter (fun p => Y p ⊆ bundle_of σ j)
  have hp0_not_in_P : p0 ∉ P_sub := fun h => hp0_not_sub (mem_filter.mp h).2
  have hP_sub_card : P_sub.card ≤ n - 2 := by
    have h_sub : P_sub ⊆ univ.erase p0 := by
      intro p hp
      rw [mem_erase]
      exact ⟨fun h => hp0_not_in_P (h ▸ hp), mem_univ _⟩
    have h_le := card_le_card h_sub
    rw [card_erase_of_mem (mem_univ p0), card_univ, Fintype.card_fin] at h_le
    omega
  set X : Finset (Fin m) := P_sub.biUnion (fun p => eefx_bundle_imp_approx_efk_pick_one (Y p))
  have hX_sub_Aj : X ⊆ bundle_of σ j := by
    intro x hx
    rw [mem_biUnion] at hx
    rcases hx with ⟨p, hp, hx_pick⟩
    have hp_sub : Y p ⊆ bundle_of σ j := (mem_filter.mp hp).2
    exact hp_sub (eefx_bundle_imp_approx_efk_pick_one_subset (Y p) hx_pick)
  have hX_card : X.card ≤ n - 2 := by
    calc
      X.card ≤ ∑ p ∈ P_sub, (eefx_bundle_imp_approx_efk_pick_one (Y p)).card := card_biUnion_le
      _ ≤ ∑ p ∈ P_sub, 1 := sum_le_sum (fun p _ => eefx_bundle_imp_approx_efk_pick_one_card_le (Y p))
      _ = P_sub.card := by rw [sum_const, smul_eq_mul, mul_one]
      _ ≤ n - 2 := hP_sub_card
  have h_Aj_sub : (bundle_of σ j \ X) ⊆ univ.biUnion Y := by
    intro g hg
    have hg_j : g ∈ bundle_of σ j := (mem_sdiff.mp hg).1
    have hg_σ_j : σ g = j := by
      unfold bundle_of at hg_j
      simp only [mem_filter, mem_univ, true_and] at hg_j
      exact hg_j
    have hg_not_i_2 : g ∉ bundle_of σ i := by
      unfold bundle_of
      simp only [mem_filter, mem_univ, true_and]
      intro h
      exact hij (hg_σ_j.symm.trans h).symm
    rw [hY_union, mem_sdiff]
    exact ⟨mem_univ _, hg_not_i_2⟩
  have h_sum_split := eefx_bundle_imp_approx_efk_sum_val_partition (u i) (bundle_of σ j \ X) Y hY_disj h_Aj_sub
  have h_term_le : ∀ p : Fin (n - 1),
      additive_valuation (u i) ((bundle_of σ j \ X) ∩ Y p) ≤ additive_valuation (u i) (bundle_of σ i) := by
    intro p
    exact eefx_bundle_imp_approx_efk_part_val_le (u i) (hu i) (bundle_of σ i) (bundle_of σ j) Y hY_bound P_sub
      (fun q => mem_filter.trans (and_iff_right (mem_univ q))) X rfl p
  have h_val_le : additive_valuation (u i) (bundle_of σ j \ X) ≤ ((n : ℝ) - 1) * additive_valuation (u i) (bundle_of σ i) := by
    rw [h_sum_split]
    calc
      ∑ p : Fin (n - 1), additive_valuation (u i) ((bundle_of σ j \ X) ∩ Y p)
        ≤ ∑ _p : Fin (n - 1), additive_valuation (u i) (bundle_of σ i) := sum_le_sum (fun p _ => h_term_le p)
      _ = ((n : ℝ) - 1) * additive_valuation (u i) (bundle_of σ i) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : 1 ≤ n := by omega
        rw [Nat.cast_sub h1]
        push_cast
        rfl
  have h_rem_le : bundle_remove_k_value (additive_valuation (u i)) (n - 2) (bundle_of σ j) ≤
      additive_valuation (u i) (bundle_of σ j \ X) :=
    bundle_remove_k_value_le (additive_valuation (u i)) (n - 2) (bundle_of σ j) X hX_sub_Aj hX_card
  have h_trans : bundle_remove_k_value (additive_valuation (u i)) (n - 2) (bundle_of σ j) ≤
      ((n : ℝ) - 1) * additive_valuation (u i) (bundle_of σ i) :=
    h_rem_le.trans h_val_le
  have hn_pos : 0 < (n : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_iff₀ hn_pos).mpr (by linarith)
