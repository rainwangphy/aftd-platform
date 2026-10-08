import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.xBy_swap

Topic: equilibria   Node: f45a303d47d6

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.xBy_swap`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bilinear pairing `xBy` and its symmetric variants.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- The bilinear pairing `xBy` and its symmetric variants. -/
theorem Loomis.xBy_swap (B : I → J → ℝ)
    (x : stdSimplex ℝ I) (y : stdSimplex ℝ J) :
    wsum x (fun i => By B y i) = wsum y (fun j => xB B x j) := by
  unfold xB By
  exact wsum_wsum_comm x y B
