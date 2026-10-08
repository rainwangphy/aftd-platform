import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.mu0

Topic: equilibria   Node: 1fc3a427260a

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.mu0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Player II's minmax value (the column player's best cap).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Player II's minmax value (the column player's best cap). -/
noncomputable def MinimaxLoomis.mu0 (A : I → J → ℝ) : ℝ := iInf (mu.aux A)
