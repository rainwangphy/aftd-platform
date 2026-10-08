import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsConstantSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.isZeroSum_iff_isConstantSum_zero

Topic: equilibria   Node: cbe3d66abb5d

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.isZeroSum_iff_isConstantSum_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

`IsZeroSum G` and `IsConstantSum G 0` are the same proposition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- `IsZeroSum G` and `IsConstantSum G 0` are the same proposition. -/
theorem EconCSLib.StrategicGame.isZeroSum_iff_isConstantSum_zero [Add U] [Zero U]
    {G : EconCSLib.StrategicGame (Fin 2) U} :
    IsZeroSum G ↔ IsConstantSum G 0 :=
  Iff.rfl
