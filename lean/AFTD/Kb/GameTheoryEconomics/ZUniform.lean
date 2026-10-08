import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex

/-!
# z_uniform

Topic: general_equilibrium   Node: b2beb9937bff

Provenance: formalization of a published result. Source: EconCSLib, `z_uniform`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The uniform point in the big simplex.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- The uniform point in the big simplex. -/
noncomputable def z_uniform : BigSimplex card :=
  ⟨fun _ => (1 : ℝ) / (total_card card : ℝ), by
    simp only [stdSimplex, Set.mem_setOf_eq]
    constructor
    · intro _; apply div_nonneg; norm_num;
      have : 0 < (total_card card : ℝ) := by
        norm_cast; exact PNat.pos (total_card card)
      exact le_of_lt this
    · have hpos : 0 < (total_card card : ℝ) := by
        norm_cast; exact PNat.pos (total_card card)
      have hcard : (Fintype.card (Fin (total_card card)) : ℝ) = (total_card card : ℝ) := by
        simp
      simp [Finset.sum_const, (ne_of_gt hpos)]
  ⟩
