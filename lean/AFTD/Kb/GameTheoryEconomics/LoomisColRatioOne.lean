import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.LoomisXBOne
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.colRatio_one

Topic: equilibria   Node: b136b513fb17

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.colRatio_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.colRatio_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.colRatio_one (A : I → J → ℝ) (x : stdSimplex ℝ I) (j : J) :
    colRatio A (fun _ _ => 1) x j = wsum x (fun i => A i j) := by
  unfold colRatio
  rw [xB_one]
  unfold xA
  exact div_one _
