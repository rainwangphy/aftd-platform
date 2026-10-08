import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.IsZeroSum.decidable

Topic: equilibria   Node: 4a343f51c48c

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsZeroSum.decidable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

StrategicGame.IsZeroSum.decidable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
instance EconCSLib.StrategicGame.IsZeroSum.decidable [Add U] [Zero U] [DecidableEq U]
    {G : EconCSLib.StrategicGame (Fin 2) U}
    [∀ i, Fintype (G.strategy i)] :
    Decidable (IsZeroSum G) :=
  Fintype.decidableForallFintype
