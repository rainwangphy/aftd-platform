import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeI

/-!
# MatrixGame.dualityGap

Topic: equilibria   Node: 1925a9469938

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.dualityGap`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Point-wise duality gap** at a strategy pair: the column player's realised loss-cap minus the row player's realised guarantee. Always nonnegative, zero exactly at optimal pairs. Field-generic: just the difference of two L2 guarantees, no sup/inf.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Point-wise duality gap** at a strategy pair: the column player's realised loss-cap minus the row player's realised guarantee. Always nonnegative, zero exactly at optimal pairs. Field-generic: just the difference of two L2 guarantees, no sup/inf. -/
noncomputable def MatrixGame.dualityGap {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) : 𝕜 :=
  A.guarantee_II yy - A.guarantee_I xx
