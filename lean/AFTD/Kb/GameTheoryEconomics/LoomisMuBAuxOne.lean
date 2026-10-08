import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatio
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatioOne
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.muB.aux_one

Topic: equilibria   Node: 8729410cb1e5

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.muB.aux_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.muB.aux_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.muB.aux_one (A : I → J → ℝ) (y : stdSimplex ℝ J) :
    muB.aux A (fun _ _ => 1) y = MinimaxLoomis.mu.aux A y := by
  unfold muB.aux MinimaxLoomis.mu.aux
  congr 1; ext i
  exact rowRatio_one A y i
