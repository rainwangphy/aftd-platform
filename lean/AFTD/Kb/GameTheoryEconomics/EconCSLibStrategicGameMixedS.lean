import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.MixedS

Topic: equilibria   Node: 277776c03e3f

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.MixedS`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Type abbreviation for the product of standard simplices (one per player), used throughout this file. Defined as an `abbrev` so Lean unfolds it automatically for topology and continuity instances.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Function in
set_option linter.unusedSectionVars false in
variable {N : Type*} in
variable (G : EconCSLib.StrategicGame N ℝ) in
variable [Fintype N] [DecidableEq N] in
variable [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)] in
variable [∀ i, Inhabited (G.strategy i)] in
/-- Type abbreviation for the product of standard simplices (one per player), used throughout this file. Defined as an `abbrev` so Lean unfolds it automatically for topology and continuity instances. -/
noncomputable abbrev EconCSLib.StrategicGame.MixedS := ∀ i, stdSimplex ℝ (G.strategy i)
