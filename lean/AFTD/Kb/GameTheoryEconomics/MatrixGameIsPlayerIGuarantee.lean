import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGameMaximin

/-!
# MatrixGame.IsPlayerIGuarantee

Topic: equilibria   Node: 63b73529f12d

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsPlayerIGuarantee`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`w` is a **guarantee for player I** when some mixed row strategy achieves expected payoff `≥ w` against every pure column. Equivalent to `w ≤ A.maximin`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- `w` is a **guarantee for player I** when some mixed row strategy achieves expected payoff `≥ w` against every pure column. Equivalent to `w ≤ A.maximin`. -/
def MatrixGame.IsPlayerIGuarantee {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (w : 𝕜) : Prop :=
  ∃ xx : stdSimplex 𝕜 I, ∀ j, w ≤ A.Ej xx j
