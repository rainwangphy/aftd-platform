import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisColRatioOne
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB.aux_one

Topic: equilibria   Node: 270e2681fb42

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB.aux_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.lamB.aux_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.lamB.aux_one (A : I → J → ℝ) (x : stdSimplex ℝ I) :
    lamB.aux A (fun _ _ => 1) x = MinimaxLoomis.lam.aux A x := by
  unfold lamB.aux MinimaxLoomis.lam.aux
  congr 1; ext j
  exact colRatio_one A x j
