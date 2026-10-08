import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.TPush
import AFTD.Kb.GameTheoryEconomics.ZUniform
import AFTD.Kb.GameTheoryEconomics.Deficit
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.BlockSum

/-!
# pushTowardsZ

Topic: general_equilibrium   Node: 22847d35c0e7

Provenance: formalization of a published result. Source: EconCSLib, `pushTowardsZ`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convex push of `x` toward `z_uniform` by amount `tPush`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Convex push of `x` toward `z_uniform` by amount `tPush`. -/
noncomputable def pushTowardsZ (x : BigSimplex card) : BigSimplex card :=
  ⟨fun k => (1 - tPush card x) * x.1 k + (tPush card x) * (z_uniform card).1 k, by
    simp only [stdSimplex, Set.mem_setOf_eq]
    constructor
    · intro k;
      have hx_nonneg : 0 ≤ x.1 k := x.2.1 k
      have hz_nonneg : 0 ≤ (z_uniform card).1 k := (z_uniform card).2.1 k
      have h_def_nonneg : 0 ≤ deficit card x := by
        unfold deficit
        apply Finset.sum_nonneg
        intro i _
        exact le_max_left _ _
      have hden_pos : 0 < (1 : ℝ) + deficit card x :=
        add_pos_of_pos_of_nonneg (by norm_num) h_def_nonneg
      have ht_nonneg : 0 ≤ tPush card x := by
        simpa [tPush] using div_nonneg h_def_nonneg (le_of_lt hden_pos)
      have h_t_le_one : tPush card x ≤ 1 := by
        have hle : deficit card x ≤ 1 + deficit card x := by linarith
        have hinv_nonneg : 0 ≤ (1 + deficit card x)⁻¹ :=
          inv_nonneg.mpr (le_of_lt hden_pos)
        have hmul := mul_le_mul_of_nonneg_right hle hinv_nonneg
        have hdiv :
            (deficit card x) / (1 + deficit card x) ≤
              (1 + deficit card x) / (1 + deficit card x) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
        simpa [tPush, div_self (ne_of_gt hden_pos)] using hdiv
      have hone_minus_nonneg : 0 ≤ 1 - tPush card x := by linarith
      have hterm1 : 0 ≤ (1 - tPush card x) * x.1 k := mul_nonneg hone_minus_nonneg hx_nonneg
      have hterm2 : 0 ≤ (tPush card x) * (z_uniform card).1 k := mul_nonneg ht_nonneg hz_nonneg
      exact add_nonneg hterm1 hterm2
    · classical
      have hpos_tc : 0 < (total_card card : ℝ) := by
        norm_cast; exact PNat.pos (total_card card)
      have hx_sum_all : (∑ k, x.1 k) = 1 := x.2.2
      have hz_sum_all : (∑ k, (z_uniform card).1 k) = 1 := by
        simp [z_uniform, Finset.sum_const, (ne_of_gt hpos_tc)]
      have hx_sum : (∑ k ∈ Finset.univ, x.1 k) = 1 := by simpa using hx_sum_all
      have hz_sum : (∑ k ∈ Finset.univ, (z_uniform card).1 k) = 1 := by simpa using hz_sum_all
      calc
        (∑ k ∈ Finset.univ, ((1 - tPush card x) * x.1 k + (tPush card x) * (z_uniform card).1 k))
            = (1 - tPush card x) * (∑ k ∈ Finset.univ, x.1 k) + (tPush card x) * (∑ k ∈ Finset.univ, (z_uniform card).1 k) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum]
        _ = 1 := by
              simp [hx_sum, hz_sum]
  ⟩
