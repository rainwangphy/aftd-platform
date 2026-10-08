import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.TPush
import AFTD.Kb.GameTheoryEconomics.Deficit
import AFTD.Kb.GameTheoryEconomics.DeficitNonneg

/-!
# tPush_mem_Icc

Topic: general_equilibrium   Node: 9afd2c2bfa43

Provenance: formalization of a published result. Source: EconCSLib, `tPush_mem_Icc`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`tPush card x` is always in `[0, 1]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- `tPush card x` is always in `[0, 1]`. -/
lemma tPush_mem_Icc (x : BigSimplex card) : tPush card x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have hden : 0 ≤ (1 : ℝ) + deficit card x := by
      have := deficit_nonneg card x; linarith
    simpa [tPush] using div_nonneg (deficit_nonneg card x) hden
  · have hdenpos : 0 < (1 : ℝ) + deficit card x := by
      have := deficit_nonneg card x
      exact add_pos_of_pos_of_nonneg (by norm_num) this
    have hle : deficit card x ≤ 1 + deficit card x := by linarith
    have hinv_nonneg : 0 ≤ (1 + deficit card x)⁻¹ := inv_nonneg.mpr (le_of_lt hdenpos)
    have := mul_le_mul_of_nonneg_right hle hinv_nonneg
    have : (deficit card x) / (1 + deficit card x) ≤ (1 + deficit card x) / (1 + deficit card x) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [tPush, div_self (ne_of_gt hdenpos)] using this
