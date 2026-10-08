import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropRow
import AFTD.Kb.GameTheoryEconomics.LoomisDropRow
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisWsumExtendDropRow
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.xB_extendDropRow

Topic: equilibria   Node: 0167a8ba427e

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.xB_extendDropRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.xB_extendDropRow
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.xB_extendDropRow [DecidableEq I] (j : J) (B : I → J → ℝ)
    (i₀ : I) (x' : stdSimplex ℝ {i : I // i ≠ i₀}) :
    xB B (MinimaxLoomis.extendDropRow i₀ x') j = xB (dropRow B i₀) x' j := by
  unfold xB
  rw [MinimaxLoomis.wsum_extendDropRow]
  rfl
