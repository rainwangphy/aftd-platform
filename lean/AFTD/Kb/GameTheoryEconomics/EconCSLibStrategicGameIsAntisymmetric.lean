import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsAntisymmetric

Topic: equilibria   Node: a47b8136b316

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.IsAntisymmetric`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Antisymmetric.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A square matrix is **antisymmetric** if `B i j = -B j i` for all `i, j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- A square matrix is **antisymmetric** if `B i j = -B j i` for all `i, j`. -/
def EconCSLib.StrategicGame.IsAntisymmetric (B : I → I → ℝ) : Prop := ∀ i j, B i j = -B j i
