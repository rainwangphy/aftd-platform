import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB0

Topic: equilibria   Node: f4deba22cdce

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Maxmin Loomis scalar `λ₀ = sup_x λ_aux(x)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Maxmin Loomis scalar `λ₀ = sup_x λ_aux(x)`. -/
noncomputable def Loomis.lamB0 (A B : I → J → ℝ) : ℝ := iSup (lamB.aux A B)
