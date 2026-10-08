import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropRow
import AFTD.Kb.GameTheoryEconomics.LoomisDropRow
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisWsumExtendDropRow
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.xA_extendDropRow

Topic: equilibria   Node: 4ba02c70f626

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.xA_extendDropRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.xA_extendDropRow
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.xA_extendDropRow [DecidableEq I] (j : J) (A : I → J → ℝ)
    (i₀ : I) (x' : stdSimplex ℝ {i : I // i ≠ i₀}) :
    xA A (MinimaxLoomis.extendDropRow i₀ x') j = xA (dropRow A i₀) x' j := by
  unfold xA
  rw [MinimaxLoomis.wsum_extendDropRow]
  rfl
