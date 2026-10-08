import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi

/-!
# MatrixGame.guarantee_II

Topic: equilibria   Node: 4243bded20d6

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.guarantee_II`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Player II's guaranteed loss using mixed strategy `y`: the maximum expected payoff (for Player I) over all of Player I's pure responses.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable (A : MatrixGame I J 𝕜) in
/-- Player II's guaranteed loss using mixed strategy `y`: the maximum expected payoff (for Player I) over all of Player I's pure responses. -/
noncomputable def MatrixGame.guarantee_II (y : stdSimplex 𝕜 J) : 𝕜 :=
  Finset.sup' univ Finset.univ_nonempty (fun i => A.Ei i y)
