import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisColOffset
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxGtIffGt
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.LoomisXBPos
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB.aux_gt_of_colOffset_pos

Topic: equilibria   Node: 864f3884699d

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB.aux_gt_of_colOffset_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`lamB.aux A B x` strictly exceeds `lam` iff every offset `colOffset` is strictly positive at `x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `lamB.aux A B x` strictly exceeds `lam` iff every offset `colOffset` is strictly positive at `x`. -/
theorem Loomis.lamB.aux_gt_of_colOffset_pos {A B : I → J → ℝ}
    (hB : IsPositive B) {lam : ℝ} {x : stdSimplex ℝ I}
    (H : ∀ j, 0 < colOffset A B lam x j) :
    lam < lamB.aux A B x := by
  rw [lamB.aux_gt_iff_gt]
  intro j
  unfold colRatio
  rw [lt_div_iff₀ (xB_pos hB x j)]
  -- Goal: lam * xB B x j < xA A x j
  have := H j
  unfold colOffset at this
  linarith
