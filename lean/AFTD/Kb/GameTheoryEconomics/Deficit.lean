import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.BlockWeight
import AFTD.Kb.GameTheoryEconomics.BlockSum

/-!
# deficit

Topic: general_equilibrium   Node: 7032f29bed74

Provenance: formalization of a published result. Source: EconCSLib, `deficit`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total positive shortfall of block sums relative to block weights.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Total positive shortfall of block sums relative to block weights. -/
noncomputable def deficit (x : BigSimplex card) : ℝ :=
  ∑ i, max (0 : ℝ) ((blockWeight card i) - blockSum card i x)
