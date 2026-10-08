import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.xB

Topic: equilibria   Node: 8b7d77a2c49b

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.xB`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Row-vector product `(xB)_j = ∑ᵢ xᵢ Bᵢⱼ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Row-vector product `(xB)_j = ∑ᵢ xᵢ Bᵢⱼ`. -/
noncomputable def Loomis.xB (B : I → J → ℝ) (x : stdSimplex ℝ I) (j : J) : ℝ :=
  wsum x (fun i => B i j)
