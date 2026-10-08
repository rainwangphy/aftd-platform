import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameMaximin
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimax
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLam0LeMu0
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.maximin_le_minimax

Topic: equilibria   Node: 56355422d070

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.maximin_le_minimax`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Maximin ≤ minimax (always holds, for any matrix game). This is the finite weak-duality inequality.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- Maximin ≤ minimax (always holds, for any matrix game). This is the finite weak-duality inequality. -/
theorem MatrixGame.maximin_le_minimax : A.maximin ≤ A.minimax :=
  MinimaxLoomis.lam0_le_mu0 A.g
