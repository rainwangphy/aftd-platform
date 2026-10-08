import AFTD.Prelude

/-!
# MatrixGame

Topic: equilibria   Node: 69c344fd03c1

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite two-player zero-sum matrix game. Player I chooses row `i : I`, Player II chooses column `j : J`. Payoff to Player I is `g i j` (in the scalar field `𝕜`); payoff to Player II is `-g i j`. The scalar field `𝕜` defaults to `ℚ` so that unannotated `MatrixGame I J` means a rational matrix game — keeping the data structure Bourbaki-minimal and forcing the choice of `ℝ` (or any other ordered field) to be explicit at the use site.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
/-- A finite two-player zero-sum matrix game. Player I chooses row `i : I`, Player II chooses column `j : J`. Payoff to Player I is `g i j` (in the scalar field `𝕜`); payoff to Player II is `-g i j`. The scalar field `𝕜` defaults to `ℚ` so that unannotated `MatrixGame I J` means a rational matrix game — keeping the data structure Bourbaki-minimal and forcing the choice of `ℝ` (or any other ordered field) to be explicit at the use site. -/
structure MatrixGame (I J : Type*) (𝕜 : Type := ℚ) where
  /-- The payoff matrix. -/
  g : I → J → 𝕜
