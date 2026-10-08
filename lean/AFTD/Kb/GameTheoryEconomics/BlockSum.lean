import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.IndexCombine

/-!
# blockSum

Topic: general_equilibrium   Node: 599989367fb3

Provenance: formalization of a published result. Source: EconCSLib, `blockSum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Sum of coordinates of `x` over the block `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Sum of coordinates of `x` over the block `i`. -/
noncomputable def blockSum (i : I) (x : BigSimplex card) : ℝ :=
  ∑ j : Fin (card i), x.1 (index_combine card ⟨i, j⟩)
