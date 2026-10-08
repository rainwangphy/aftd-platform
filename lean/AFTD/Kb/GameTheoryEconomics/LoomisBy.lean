import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.By

Topic: equilibria   Node: 0d4d6414b46e

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.By`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Column-vector product `(By)_i = ∑ⱼ Bᵢⱼ yⱼ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Column-vector product `(By)_i = ∑ⱼ Bᵢⱼ yⱼ`. -/
noncomputable def Loomis.By (B : I → J → ℝ) (y : stdSimplex ℝ J) (i : I) : ℝ :=
  wsum y (fun j => B i j)
