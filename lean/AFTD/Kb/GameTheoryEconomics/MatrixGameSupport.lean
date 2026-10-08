import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame

/-!
# MatrixGame.support

Topic: equilibria   Node: 7051a59642aa

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.support`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Support** of a mixed strategy: the indices with positive probability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Support** of a mixed strategy: the indices with positive probability. -/
noncomputable def MatrixGame.support {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [DecidableEq I] (xx : stdSimplex 𝕜 I) : Finset I :=
  Finset.univ.filter (fun i => 0 < xx.val i)
