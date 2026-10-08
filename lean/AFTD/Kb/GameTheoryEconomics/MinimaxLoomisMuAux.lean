import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.mu.aux

Topic: equilibria   Node: 8a36c774f051

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.mu.aux`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Player II's maximum loss against mixed strategy `y`: the maximum over pure rows of the expected payoff.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Player II's maximum loss against mixed strategy `y`: the maximum over pure rows of the expected payoff. -/
noncomputable def MinimaxLoomis.mu.aux (A : I → J → ℝ) (y : stdSimplex ℝ J) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun i => wsum y (fun j => A i j))
