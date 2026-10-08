import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropColumn
import AFTD.Kb.GameTheoryEconomics.LoomisDropCol
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisWsumExtendDropColumn
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.By_extendDropColumn

Topic: equilibria   Node: 12bda78c72ba

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.By_extendDropColumn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.By_extendDropColumn
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.By_extendDropColumn [DecidableEq J] (i : I) (B : I → J → ℝ)
    (j₀ : J) (y' : stdSimplex ℝ {j : J // j ≠ j₀}) :
    By B (MinimaxLoomis.extendDropColumn j₀ y') i = By (dropCol B j₀) y' i := by
  unfold By
  rw [MinimaxLoomis.wsum_extendDropColumn]
  rfl
