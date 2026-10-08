import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsConstantSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.IsConstantSum.zero_isZeroSum

Topic: equilibria   Node: f671e794fa90

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsConstantSum.zero_isZeroSum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A constant-sum game whose constant is `0` is zero-sum.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- A constant-sum game whose constant is `0` is zero-sum. -/
theorem EconCSLib.StrategicGame.IsConstantSum.zero_isZeroSum [Add U] [Zero U]
    {G : EconCSLib.StrategicGame (Fin 2) U} (h : IsConstantSum G 0) :
    IsZeroSum G := h
