import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.PushTowardsZ
import AFTD.Kb.GameTheoryEconomics.IndexCombine
import AFTD.Kb.GameTheoryEconomics.BlockSum
import AFTD.Kb.GameTheoryEconomics.TPush
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.ZUniform
import AFTD.Kb.GameTheoryEconomics.Deficit
import AFTD.Kb.GameTheoryEconomics.ProductSimplices

/-!
# project_to_product

Topic: general_equilibrium   Node: 5773863f1441

Provenance: formalization of a published result. Source: EconCSLib, `project_to_product`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Retraction from the big simplex to the product of simplices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Retraction from the big simplex to the product of simplices. -/
noncomputable def project_to_product (x : BigSimplex card) : ProductSimplices card :=
  fun i =>
    let y := pushTowardsZ card x
    let s := blockSum card i y
    have hspos : 0 < s := by
      classical
      have h_sum_eq :
          blockSum card i y =
            (1 - tPush card x) * blockSum card i x +
            (tPush card x) * blockWeight card i := by
        simp only [blockSum, y, pushTowardsZ, z_uniform, blockWeight, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.sum_const, sub_eq_add_neg, Finset.card_fin]
        ring_nf

      have h_bw_pos : 0 < blockWeight card i := by
        unfold blockWeight
        have htc : 0 < (total_card card : ℝ) := by norm_cast; exact PNat.pos (total_card card)
        have hci : 0 < (card i : ℝ) := by norm_cast; exact PNat.pos (card i)
        exact div_pos hci htc

      have h_block_nonneg : 0 ≤ blockSum card i x := by
        unfold blockSum; apply Finset.sum_nonneg; intro j _; exact x.2.1 _
      have h_def_nonneg : 0 ≤ deficit card x := by
        unfold deficit; apply Finset.sum_nonneg; intro i' _; exact le_max_left _ _
      have h_t_nonneg : 0 ≤ tPush card x := by
        have hden : 0 ≤ (1 : ℝ) + deficit card x := by linarith
        simpa [tPush] using div_nonneg h_def_nonneg hden
      have h_t_le_one : tPush card x ≤ 1 := by
        have hdenpos : 0 < (1 : ℝ) + deficit card x := by
          exact add_pos_of_pos_of_nonneg (by norm_num) h_def_nonneg
        have hle : deficit card x ≤ 1 + deficit card x := by linarith
        have hinv_nonneg : 0 ≤ (1 + deficit card x)⁻¹ := inv_nonneg.mpr (le_of_lt hdenpos)
        have := mul_le_mul_of_nonneg_right hle hinv_nonneg
        have h_div_le : (deficit card x) / (1 + deficit card x) ≤ (1 + deficit card x) / (1 + deficit card x) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
        simpa [tPush, div_self (ne_of_gt hdenpos)] using h_div_le

      have h_one_minus_nonneg : 0 ≤ 1 - tPush card x := by linarith
      by_cases ht0 : tPush card x = 0
      · have h_def0 : deficit card x = 0 := by
          have hden_pos : 0 < 1 + deficit card x := add_pos_of_pos_of_nonneg (by norm_num) h_def_nonneg
          exact (div_eq_zero_iff.mp ht0).resolve_right (ne_of_gt hden_pos)
        have h_term_le_sum : max 0 (blockWeight card i - blockSum card i x) ≤ deficit card x := by
          classical
          have hnonneg : ∀ i' ∈ (Finset.univ : Finset I), 0 ≤ max 0 (blockWeight card i' - blockSum card i' x) :=
            fun i' _ => le_max_left _ _
          simpa [deficit] using Finset.single_le_sum hnonneg (by simp)
        have h_term_zero : max 0 (blockWeight card i - blockSum card i x) = 0 := by
          exact le_antisymm (h_term_le_sum.trans (le_of_eq h_def0)) (le_max_left _ _)
        have h_bw_le_sum : blockWeight card i ≤ blockSum card i x := by
          simpa [sub_nonpos] using (max_eq_left_iff.1 h_term_zero)
        have : 0 < blockSum card i x := lt_of_lt_of_le h_bw_pos h_bw_le_sum
        have hxpos : 0 < blockSum card i x := lt_of_lt_of_le h_bw_pos h_bw_le_sum
        have hypos : 0 < blockSum card i y := by
          simpa [h_sum_eq, ht0] using hxpos
        simpa [s] using hypos
      · have htpos : 0 < tPush card x := lt_of_le_of_ne h_t_nonneg (Ne.symm ht0)
        have : 0 < (tPush card x) * blockWeight card i := mul_pos htpos h_bw_pos
        have hge : (tPush card x) * blockWeight card i ≤ blockSum card i y := by
          have hfirst : 0 ≤ (1 - tPush card x) * blockSum card i x :=
            mul_nonneg h_one_minus_nonneg h_block_nonneg
          linarith [h_sum_eq, hfirst]
        exact lt_of_lt_of_le this hge
    (⟨fun j => y.1 (index_combine card ⟨i, j⟩) / s, by
      simp only [stdSimplex, Set.mem_setOf_eq]
      constructor
      · intro j
        have hy := y.2.1 (index_combine card ⟨i, j⟩)
        exact div_nonneg hy (le_of_lt hspos)
      · classical
        have h :
           (∑ j : Fin (card i), y.1 (index_combine card ⟨i, j⟩) / s)
             = (∑ j : Fin (card i), y.1 (index_combine card ⟨i, j⟩)) * s⁻¹ := by
         simp [div_eq_mul_inv, Finset.sum_mul]
        have hsum : (∑ j : Fin (card i), y.1 (index_combine card ⟨i, j⟩)) = s := rfl
        rw [h, hsum]
        field_simp
    ⟩ : stdSimplex ℝ (Fin (card i)))
