import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII

/-!
# MatrixGame.minimax

Topic: equilibria   Node: edf9269d9e76

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.minimax`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The minimax value: the best guarantee Player II can achieve. `minimax = inf_y sup_i E(i, y)`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] in
variable (A : MatrixGame I J 𝕜) in
/-- The minimax value: the best guarantee Player II can achieve. `minimax = inf_y sup_i E(i, y)` -/
noncomputable def MatrixGame.minimax : 𝕜 :=
  iInf (fun y => A.guarantee_II y)
