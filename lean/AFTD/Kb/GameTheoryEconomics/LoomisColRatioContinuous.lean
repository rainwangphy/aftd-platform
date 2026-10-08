import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumContinuous
import AFTD.Kb.GameTheoryEconomics.LoomisXBPos
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.colRatio.continuous

Topic: equilibria   Node: fb45f042c648

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.colRatio.continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Each column ratio `(xA)_j / (xB)_j` is continuous on `Δ(I)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Each column ratio `(xA)_j / (xB)_j` is continuous on `Δ(I)`. -/
theorem Loomis.colRatio.continuous {A B : I → J → ℝ} (hB : IsPositive B) (j : J) :
    Continuous (fun x : stdSimplex ℝ I => colRatio A B x j) := by
  unfold colRatio xA xB
  exact (wsum_continuous (fun i => A i j)).div
    (wsum_continuous (fun i => B i j))
    (fun x => (xB_pos hB x j).ne')
