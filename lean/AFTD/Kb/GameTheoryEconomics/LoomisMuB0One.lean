import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMu0
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxOne
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.muB0_one

Topic: equilibria   Node: 0b0ea4cf0aee

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.muB0_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.muB0_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.muB0_one (A : I → J → ℝ) :
    muB0 A (fun _ _ => 1) = MinimaxLoomis.mu0 A := by
  unfold muB0 MinimaxLoomis.mu0
  exact iInf_congr (muB.aux_one A)
