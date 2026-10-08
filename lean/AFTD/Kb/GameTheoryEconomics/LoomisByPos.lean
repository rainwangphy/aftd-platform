import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.Optimization.WsumPos
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.By_pos

Topic: equilibria   Node: c9f9ea143163

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.By_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positivity of the column aggregate when `B` is entrywise positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Positivity of the column aggregate when `B` is entrywise positive. -/
theorem Loomis.By_pos {B : I → J → ℝ} (hB : IsPositive B)
    (y : stdSimplex ℝ J) (i : I) : 0 < By B y i :=
  wsum_pos y (fun j => hB i j)
