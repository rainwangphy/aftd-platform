import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.BlockSum
import AFTD.Kb.GameTheoryEconomics.IndexCombine

/-!
# blockSum_nonneg

Topic: general_equilibrium   Node: ee507e32dc6c

Provenance: formalization of a published result. Source: EconCSLib, `blockSum_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`blockSum card i x` is always nonnegative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- `blockSum card i x` is always nonnegative. -/
lemma blockSum_nonneg (i : I) (x : BigSimplex card) : 0 ≤ blockSum card i x := by
  unfold blockSum
  apply Finset.sum_nonneg
  intro j _
  exact x.2.1 _
