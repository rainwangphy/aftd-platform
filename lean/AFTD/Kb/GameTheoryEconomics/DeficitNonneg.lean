import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.Deficit
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.BlockSum

/-!
# deficit_nonneg

Topic: general_equilibrium   Node: 05da54b12929

Provenance: formalization of a published result. Source: EconCSLib, `deficit_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`deficit card x` is always nonnegative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- `deficit card x` is always nonnegative. -/
lemma deficit_nonneg (x : BigSimplex card) : 0 ≤ deficit card x := by
  unfold deficit
  apply Finset.sum_nonneg
  intro i _
  exact le_max_left _ _
