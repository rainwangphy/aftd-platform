import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsMixedNashEq
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsSaddlePoint

/-!
# MatrixGame.isMixedNashEq_iff_isSaddlePoint

Topic: equilibria   Node: 36211ed59836

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.isMixedNashEq_iff_isSaddlePoint`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Nash equilibrium ↔ saddle point** for matrix games. Both sides unfold to the same saddle-point inequality system; the equivalence is therefore definitional.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Nash equilibrium ↔ saddle point** for matrix games. Both sides unfold to the same saddle-point inequality system; the equivalence is therefore definitional. -/
theorem MatrixGame.isMixedNashEq_iff_isSaddlePoint
    {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) :
    A.IsMixedNashEq xx yy ↔ A.IsSaddlePoint xx yy := Iff.rfl
