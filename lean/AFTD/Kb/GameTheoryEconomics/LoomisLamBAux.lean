import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB.aux

Topic: equilibria   Node: 691875183dad

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB.aux`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Player I's guaranteed Loomis ratio under mixed strategy `x`: infimum over pure columns.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Player I's guaranteed Loomis ratio under mixed strategy `x`: infimum over pure columns. -/
noncomputable def Loomis.lamB.aux (A B : I → J → ℝ) (x : stdSimplex ℝ I) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty (fun j => colRatio A B x j)
