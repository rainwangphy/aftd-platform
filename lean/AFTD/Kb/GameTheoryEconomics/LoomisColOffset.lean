import AFTD.Prelude
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.LoomisXA

/-!
# Loomis.colOffset

Topic: equilibria   Node: 87fd88fe7502

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.colOffset`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Linearised column constraint: `colOffset A B λ x j = (xA)_j - λ · (xB)_j`. Note that `colOffset A B λ x j = wsum x (fun i => A i j - λ * B i j)` is linear in `x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Linearised column constraint: `colOffset A B λ x j = (xA)_j - λ · (xB)_j`. Note that `colOffset A B λ x j = wsum x (fun i => A i j - λ * B i j)` is linear in `x`. -/
noncomputable def Loomis.colOffset (A B : I → J → ℝ) (lam : ℝ)
    (x : stdSimplex ℝ I) (j : J) : ℝ :=
  xA A x j - lam * xB B x j
