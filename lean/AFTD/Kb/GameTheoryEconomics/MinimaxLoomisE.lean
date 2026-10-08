import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.E

Topic: equilibria   Node: f746d0990a69

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.E`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected payoff of a matrix game `A : I → J → ℝ` under mixed strategies `x : stdSimplex ℝ I` and `y : stdSimplex ℝ J`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Expected payoff of a matrix game `A : I → J → ℝ` under mixed strategies `x : stdSimplex ℝ I` and `y : stdSimplex ℝ J`. -/
noncomputable def MinimaxLoomis.E (A : I → J → ℝ) (x : stdSimplex ℝ I) (y : stdSimplex ℝ J) : ℝ :=
  wsum x (fun i => wsum y (A i))
