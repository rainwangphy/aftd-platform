import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLam0
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxOne
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB0_one

Topic: equilibria   Node: d46506f0b8b4

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB0_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.lamB0_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.lamB0_one (A : I → J → ℝ) :
    lamB0 A (fun _ _ => 1) = MinimaxLoomis.lam0 A := by
  unfold lamB0 MinimaxLoomis.lam0
  exact iSup_congr (lamB.aux_one A)
