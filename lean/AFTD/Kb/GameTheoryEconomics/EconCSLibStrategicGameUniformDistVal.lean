import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformDist
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.uniformDist_val

Topic: equilibria   Node: 6cc75dfaae17

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.uniformDist_val`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.StrategicGame.uniformDist_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
@[simp] theorem EconCSLib.StrategicGame.uniformDist_val (i : I) :
    (uniformDist (I := I)).val i = (1 : ℝ) / (Fintype.card I : ℝ) := rfl
