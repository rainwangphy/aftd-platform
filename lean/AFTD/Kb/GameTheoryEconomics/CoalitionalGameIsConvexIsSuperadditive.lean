import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsConvex
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsSuperadditive

/-!
# CoalitionalGame.IsConvex.isSuperadditive

Topic: general_equilibrium   Node: 5a23a405db6e

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsConvex.isSuperadditive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convexity implies superadditivity. The `[LE U]` constraint is all that's needed beyond the section's `[AddZeroClass U]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- Convexity implies superadditivity. The `[LE U]` constraint is all that's needed beyond the section's `[AddZeroClass U]`. -/
theorem CoalitionalGame.IsConvex.isSuperadditive [LE U] (hconv : G.IsConvex) : G.IsSuperadditive := by
  intro S T hST
  have h := hconv S T
  rw [Finset.disjoint_iff_inter_eq_empty.mp hST, G.empty_zero, add_zero] at h
  exact h
