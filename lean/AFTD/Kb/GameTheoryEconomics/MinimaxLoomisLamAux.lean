import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.lam.aux

Topic: equilibria   Node: 594571fb77e3

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.lam.aux`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Player I's guaranteed payoff from mixed strategy `x`: the minimum over pure columns of the expected payoff.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Player I's guaranteed payoff from mixed strategy `x`: the minimum over pure columns of the expected payoff. -/
noncomputable def MinimaxLoomis.lam.aux (A : I → J → ℝ) (x : stdSimplex ℝ I) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty (fun j => wsum x (fun i => A i j))
