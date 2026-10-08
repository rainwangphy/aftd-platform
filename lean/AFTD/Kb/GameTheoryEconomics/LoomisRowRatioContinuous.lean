import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatio
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumContinuous
import AFTD.Kb.GameTheoryEconomics.LoomisByPos
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.rowRatio.continuous

Topic: equilibria   Node: 2d6692e00543

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.rowRatio.continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Each row ratio `(Ay)_i / (By)_i` is continuous on `Δ(J)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Each row ratio `(Ay)_i / (By)_i` is continuous on `Δ(J)`. -/
theorem Loomis.rowRatio.continuous {A B : I → J → ℝ} (hB : IsPositive B) (i : I) :
    Continuous (fun y : stdSimplex ℝ J => rowRatio A B y i) := by
  unfold rowRatio Ay By
  exact (wsum_continuous (fun j => A i j)).div
    (wsum_continuous (fun j => B i j))
    (fun y => (By_pos hB y i).ne')
