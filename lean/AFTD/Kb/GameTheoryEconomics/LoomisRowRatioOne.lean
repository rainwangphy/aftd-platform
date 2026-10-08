import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatio
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisByOne
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.rowRatio_one

Topic: equilibria   Node: a6f60ba8f26c

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.rowRatio_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.rowRatio_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.rowRatio_one (A : I → J → ℝ) (y : stdSimplex ℝ J) (i : I) :
    rowRatio A (fun _ _ => 1) y i = wsum y (fun j => A i j) := by
  unfold rowRatio
  rw [By_one]
  unfold Ay
  exact div_one _
