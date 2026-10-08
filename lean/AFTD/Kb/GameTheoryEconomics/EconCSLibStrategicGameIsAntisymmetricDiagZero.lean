import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsAntisymmetric
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsAntisymmetric.diag_zero

Topic: equilibria   Node: e3593e6c8584

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.IsAntisymmetric.diag_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Antisymmetric.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An antisymmetric matrix has zero diagonal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- An antisymmetric matrix has zero diagonal. -/
theorem EconCSLib.StrategicGame.IsAntisymmetric.diag_zero {B : I → I → ℝ} (hB : IsAntisymmetric B) (i : I) :
    B i i = 0 := by
  have := hB i i; linarith
