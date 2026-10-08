import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsConstantSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsZeroSum.toIsConstantSum

Topic: equilibria   Node: e8befb623772

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsZeroSum.toIsConstantSum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A zero-sum game is a constant-sum game with constant `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- A zero-sum game is a constant-sum game with constant `0`. -/
theorem EconCSLib.StrategicGame.IsZeroSum.toIsConstantSum [Add U] [Zero U]
    {G : EconCSLib.StrategicGame (Fin 2) U} (hzs : IsZeroSum G) :
    IsConstantSum G 0 := hzs
