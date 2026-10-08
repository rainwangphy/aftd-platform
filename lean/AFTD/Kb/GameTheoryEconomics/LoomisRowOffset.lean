import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.rowOffset

Topic: equilibria   Node: 54c3f55388d3

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.rowOffset`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Linearised row constraint: `rowOffset A B μ y i = μ · (By)_i - (Ay)_i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Linearised row constraint: `rowOffset A B μ y i = μ · (By)_i - (Ay)_i`. -/
noncomputable def Loomis.rowOffset (A B : I → J → ℝ) (mu : ℝ)
    (y : stdSimplex ℝ J) (i : I) : ℝ :=
  mu * By B y i - Ay A y i
