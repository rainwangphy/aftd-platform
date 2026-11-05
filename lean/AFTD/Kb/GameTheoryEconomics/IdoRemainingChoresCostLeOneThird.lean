import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsIdenticallyOrdered
import AFTD.Kb.GameTheoryEconomics.ChoreRemainingSet
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# ido_remaining_chores_cost_le_one_third

Topic: fair_division   Node: 4ff1e5618015

Provenance: helper lemma. arXiv:2611.04884 Lemma 4.1

In an identically ordered instance with nonnegative costs and maximin share 1 for each agent, every remaining chore g in V (with index at least 2n) has cost at most 1/3 for each agent i.
-/

/-- In an IDO instance with MMS 1, each remaining chore has cost at most 1/3. -/
lemma ido_remaining_chores_cost_le_one_third
    (n m : ℕ) (h2n : 2 * n ≤ m) (c : Fin n → Fin m → ℝ)
    (hc_nonneg : ∀ i e, 0 ≤ c i e)
    (h_ido : is_identically_ordered c)
    (h_mms : ∀ i : Fin n, chore_maximin_share n (c i) = 1)
    (i : Fin n) (g : Fin m) (hg : g ∈ chore_remaining_set m n) :
    c i g ≤ 1 / 3 := by
  have h2n_lt : 2 * n < m := by
    simp only [chore_remaining_set, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    omega
  have hg_val : 2 * n ≤ g.val := by
    simp only [chore_remaining_set, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact hg
  let b : Fin m := ⟨2 * n, h2n_lt⟩
  have hb_le_g : b ≤ g := hg_val
  have hP : ∀ P : Fin m → Fin n, 3 * c i g ≤ ⨆ k, additive_valuation (c i) (bundle_of P k) := by
    intro P
    have hmaps : ∀ a ∈ Finset.Iic b, P a ∈ (Finset.univ : Finset (Fin n)) := by simp
    have hcard : (Finset.univ : Finset (Fin n)).card * 2 < (Finset.Iic b).card := by
      rw [Finset.card_univ, Fintype.card_fin, Fin.card_Iic b]
      dsimp [b]
      omega
    obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
    let Sy := Finset.filter (fun x => P x = y) (Finset.Iic b)
    have hy' : 2 < Sy.card := hy
    have hSy_sub : Sy ⊆ bundle_of P y := by
      intro x hx
      rw [Finset.mem_filter] at hx
      simp only [Finset.mem_filter, bundle_of, Finset.mem_univ, true_and]
      exact hx.2
    have hSy_le_bundle : ∑ x ∈ Sy, c i x ≤ ∑ x ∈ bundle_of P y, c i x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSy_sub
      intro x _ _
      exact hc_nonneg i x
    have h_cg_le_x : ∀ x ∈ Sy, c i g ≤ c i x := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxb : x ≤ b := Finset.mem_Iic.mp hx.1
      have hxg : x ≤ g := le_trans hxb hb_le_g
      exact h_ido i hxg
    have h_sum_cg : (Sy.card : ℝ) * c i g ≤ ∑ x ∈ Sy, c i x := by
      have : ∑ _x ∈ Sy, c i g ≤ ∑ x ∈ Sy, c i x := Finset.sum_le_sum h_cg_le_x
      simpa using this
    have h3_card : 3 * c i g ≤ (Sy.card : ℝ) * c i g := by
      have hcig : 0 ≤ c i g := hc_nonneg i g
      have h3_le : (3 : ℝ) ≤ (Sy.card : ℝ) := by
        exact_mod_cast (show 3 ≤ Sy.card by omega)
      nlinarith
    have h3_le_bundle : 3 * c i g ≤ additive_valuation (c i) (bundle_of P y) := by
      dsimp [additive_valuation]
      linarith
    have hbundle_le_sup : additive_valuation (c i) (bundle_of P y) ≤ ⨆ k, additive_valuation (c i) (bundle_of P k) :=
      le_ciSup (Finite.bddAbove_range (fun k => additive_valuation (c i) (bundle_of P k))) y
    linarith
  have h_mms_i := h_mms i
  dsimp [chore_maximin_share] at h_mms_i
  have : Nonempty (Fin m → Fin n) := ⟨fun _ => i⟩
  have h3_le_inf : 3 * c i g ≤ ⨅ P, ⨆ k, additive_valuation (c i) (bundle_of P k) :=
    le_ciInf hP
  rw [h_mms_i] at h3_le_inf
  linarith
