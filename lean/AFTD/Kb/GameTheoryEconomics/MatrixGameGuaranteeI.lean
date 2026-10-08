import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj

/-!
# MatrixGame.guarantee_I

Topic: equilibria   Node: 736f3b898922

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.guarantee_I`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Player I's guaranteed payoff using mixed strategy `x`: the minimum expected payoff over all of Player II's pure responses. A finite `Finset.inf'` over `J`, so only `[LinearOrder 𝕜]` is needed — no order completeness.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable (A : MatrixGame I J 𝕜) in
/-- Player I's guaranteed payoff using mixed strategy `x`: the minimum expected payoff over all of Player II's pure responses. A finite `Finset.inf'` over `J`, so only `[LinearOrder 𝕜]` is needed — no order completeness. -/
noncomputable def MatrixGame.guarantee_I (x : stdSimplex 𝕜 I) : 𝕜 :=
  Finset.inf' univ Finset.univ_nonempty (fun j => A.Ej x j)
