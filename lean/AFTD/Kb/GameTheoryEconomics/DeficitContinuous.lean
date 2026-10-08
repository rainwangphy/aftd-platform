import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.Deficit
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.BlockSum
import AFTD.Kb.GameTheoryEconomics.BlockSumContinuous

/-!
# deficit_continuous

Topic: general_equilibrium   Node: 96544489594d

Provenance: formalization of a published result. Source: EconCSLib, `deficit_continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Continuity of `deficit card`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Continuity of `deficit card`. -/
lemma deficit_continuous : Continuous (deficit card) := by
  change Continuous (fun x : BigSimplex card =>
    ∑ i, max (0 : ℝ) ((blockWeight card i) - blockSum card i x))
  apply continuous_finset_sum
  intro i _
  exact continuous_const.max (continuous_const.sub (blockSum_continuous card i))
