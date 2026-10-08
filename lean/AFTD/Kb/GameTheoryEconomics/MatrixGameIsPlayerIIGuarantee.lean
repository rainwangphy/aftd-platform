import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimax

/-!
# MatrixGame.IsPlayerIIGuarantee

Topic: equilibria   Node: 23d791b1c05e

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsPlayerIIGuarantee`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`w` is a **guarantee for player II** when some mixed column strategy caps expected payoff `≤ w` against every pure row. Equivalent to `A.minimax ≤ w`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- `w` is a **guarantee for player II** when some mixed column strategy caps expected payoff `≤ w` against every pure row. Equivalent to `A.minimax ≤ w`. -/
def MatrixGame.IsPlayerIIGuarantee {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (w : 𝕜) : Prop :=
  ∃ yy : stdSimplex 𝕜 J, ∀ i, A.Ei i yy ≤ w
