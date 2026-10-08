import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.payoffAgainstRow

Topic: equilibria   Node: ecd99f20e3b8

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.payoffAgainstRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected payoff when pure row `i` faces Player II's mixed strategy `y`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable (A : MatrixGame I J 𝕜) in
/-- Expected payoff when pure row `i` faces Player II's mixed strategy `y`. -/
noncomputable def MatrixGame.payoffAgainstRow (i : I) (y : stdSimplex 𝕜 J) : 𝕜 :=
  y ⬝ᵥ A.g i
