import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.BlockSum
import AFTD.Kb.GameTheoryEconomics.PushTowardsZ
import AFTD.Kb.GameTheoryEconomics.TPush
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.IndexCombine
import AFTD.Kb.GameTheoryEconomics.ZUniform

/-!
# blockSum_pushTowardsZ_formula

Topic: general_equilibrium   Node: 473a437fd1a8

Provenance: formalization of a published result. Source: EconCSLib, `blockSum_pushTowardsZ_formula`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The block sum after pushing towards `z_uniform` follows a linear formula.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- The block sum after pushing towards `z_uniform` follows a linear formula. -/
lemma blockSum_pushTowardsZ_formula (i : I) (x : BigSimplex card) :
    blockSum card i (pushTowardsZ card x) =
      (1 - tPush card x) * blockSum card i x + (tPush card x) * blockWeight card i := by
  simp [blockSum, pushTowardsZ, sub_eq_add_neg, Finset.sum_add_distrib, Finset.mul_sum,
        z_uniform, blockWeight, div_eq_mul_inv, mul_left_comm]
