import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.rowRatio

Topic: equilibria   Node: cf0f4ab8f1a7

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.rowRatio`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Column player's per-row Loomis ratio `(Ay)_i / (By)_i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Column player's per-row Loomis ratio `(Ay)_i / (By)_i`. -/
noncomputable def Loomis.rowRatio (A B : I → J → ℝ) (y : stdSimplex ℝ J) (i : I) : ℝ :=
  Ay A y i / By B y i
