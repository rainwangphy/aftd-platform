import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB.aux_gt_iff_gt

Topic: equilibria   Node: a08e61bc9967

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB.aux_gt_iff_gt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Characterisation: `lamB.aux A B x > c` iff every column ratio exceeds `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Characterisation: `lamB.aux A B x > c` iff every column ratio exceeds `c`. -/
theorem Loomis.lamB.aux_gt_iff_gt (A B : I → J → ℝ) (c : ℝ) (x : stdSimplex ℝ I) :
    c < lamB.aux A B x ↔ ∀ j, c < colRatio A B x j := by
  simp [lamB.aux, Finset.lt_inf'_iff]
