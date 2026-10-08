import AFTD.Prelude

/-!
# EconCSLib.StrategicGame.MatrixGame.disp

Topic: equilibria   Node: 603c5b26bd91

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.MatrixGame.disp`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The displacement matrix `B i j := A i j − [i = j]` of a stochastic matrix `A`. The corresponding matrix game has value `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- The displacement matrix `B i j := A i j − [i = j]` of a stochastic matrix `A`. The corresponding matrix game has value `0`. -/
def EconCSLib.StrategicGame.MatrixGame.disp (A : I → I → ℝ) : I → I → ℝ :=
  fun i j => A i j - (if i = j then 1 else 0)
