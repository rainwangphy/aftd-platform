import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.TPush
import AFTD.Kb.GameTheoryEconomics.BlockSum
import AFTD.Kb.GameTheoryEconomics.PushTowardsZ
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.BlockSumPushTowardsZFormula
import AFTD.Kb.GameTheoryEconomics.BlockWeightPos
import AFTD.Kb.GameTheoryEconomics.BlockSumNonneg
import AFTD.Kb.GameTheoryEconomics.TPushMemIcc
import AFTD.Kb.GameTheoryEconomics.Deficit
import AFTD.Kb.GameTheoryEconomics.DeficitNonneg

/-!
# blockSum_pushTowardsZ_pos

Topic: general_equilibrium   Node: eb227bcfc288

Provenance: formalization of a published result. Source: EconCSLib, `blockSum_pushTowardsZ_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The block sum after pushing towards `z_uniform` is always positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- The block sum after pushing towards `z_uniform` is always positive. -/
lemma blockSum_pushTowardsZ_pos (i : I) (x : BigSimplex card) :
    0 < blockSum card i (pushTowardsZ card x) := by
  rw [blockSum_pushTowardsZ_formula]
  have h_bw_pos := blockWeight_pos card i
  have h_block_nonneg := blockSum_nonneg card i x
  have ⟨h_t_nonneg, h_t_le_one⟩ := tPush_mem_Icc card x
  have h_one_minus_nonneg : 0 ≤ 1 - tPush card x := by linarith
  by_cases ht0 : tPush card x = 0
  · have h_def0 : deficit card x = 0 := by
      have hden_pos : 0 < 1 + deficit card x :=
        add_pos_of_pos_of_nonneg (by norm_num) (deficit_nonneg card x)
      exact (div_eq_zero_iff.mp ht0).resolve_right (ne_of_gt hden_pos)
    have h_term_le_sum : max 0 (blockWeight card i - blockSum card i x) ≤ deficit card x := by
      classical
      have hnonneg : ∀ i' ∈ (Finset.univ : Finset I),
          0 ≤ max 0 (blockWeight card i' - blockSum card i' x) := fun i' _ => le_max_left _ _
      simpa [deficit] using Finset.single_le_sum hnonneg (by simp)
    have h_bw_le_sum : blockWeight card i ≤ blockSum card i x := by
      have h_term_zero : max 0 (blockWeight card i - blockSum card i x) = 0 :=
        le_antisymm (h_term_le_sum.trans (le_of_eq h_def0)) (le_max_left _ _)
      simpa [sub_nonpos] using (max_eq_left_iff.1 h_term_zero)
    have : 0 < blockSum card i x := lt_of_lt_of_le h_bw_pos h_bw_le_sum
    simpa [ht0] using this
  · have htpos : 0 < tPush card x := lt_of_le_of_ne h_t_nonneg (Ne.symm ht0)
    have : 0 < (tPush card x) * blockWeight card i := mul_pos htpos h_bw_pos
    linarith [mul_nonneg h_one_minus_nonneg h_block_nonneg]
