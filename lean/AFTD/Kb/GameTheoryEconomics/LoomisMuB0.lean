import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.muB0

Topic: equilibria   Node: 8125b1610a02

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.muB0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Minmax Loomis scalar `μ₀ = inf_y μ_aux(y)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Minmax Loomis scalar `μ₀ = inf_y μ_aux(y)`. -/
noncomputable def Loomis.muB0 (A B : I → J → ℝ) : ℝ := iInf (muB.aux A B)
