import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimax
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimaxTheorem

/-!
# MatrixGame.value_eq_minimax

Topic: equilibria   Node: 46251269029c

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.value_eq_minimax`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.value_eq_minimax
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
theorem MatrixGame.value_eq_minimax : A.value = A.minimax := A.minimax_theorem
