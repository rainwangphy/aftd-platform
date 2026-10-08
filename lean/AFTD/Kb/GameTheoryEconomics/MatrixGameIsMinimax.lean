import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi

/-!
# MatrixGame.IsMinimax

Topic: equilibria   Node: 09095051526b

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsMinimax`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`v` is a **minimax value** of `A`: some column strategy caps player I's payoff at `v` (existence), and no strictly smaller cap is achievable (minimality).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable (A : MatrixGame I J 𝕜) in
/-- `v` is a **minimax value** of `A`: some column strategy caps player I's payoff at `v` (existence), and no strictly smaller cap is achievable (minimality). -/
def MatrixGame.IsMinimax (A : MatrixGame I J 𝕜) (v : 𝕜) : Prop :=
  (∃ y : stdSimplex 𝕜 J, ∀ i, A.Ei i y ≤ v) ∧
  (∀ w, (∃ y : stdSimplex 𝕜 J, ∀ i, A.Ei i y ≤ w) → v ≤ w)
