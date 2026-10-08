import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.BigSimplex
import AFTD.Kb.GameTheoryEconomics.Deficit

/-!
# tPush

Topic: general_equilibrium   Node: 3b9aa2f91a8e

Provenance: formalization of a published result. Source: EconCSLib, `tPush`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Amount to push `x` toward `z_uniform` (always in `[0, 1]`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Amount to push `x` toward `z_uniform` (always in `[0, 1]`). -/
noncomputable def tPush (x : BigSimplex card) : ℝ :=
  (deficit card x) / (1 + deficit card x)
