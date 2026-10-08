import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard

/-!
# blockWeight

Topic: general_equilibrium   Node: 676e4d5335b6

Provenance: formalization of a published result. Source: EconCSLib, `blockWeight`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weight (size fraction) of block `i`: `(card i) / (total_card card)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Weight (size fraction) of block `i`: `(card i) / (total_card card)`. -/
noncomputable def blockWeight (i : I) : ℝ := (card i : ℝ) / (total_card card : ℝ)
