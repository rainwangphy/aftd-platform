import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.realisedCumPayoff

Topic: equilibria   Node: b2f3925c335c

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.realisedCumPayoff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Learning/Cesaro.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Realised cumulative payoff** along a play sequence on `A`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Filter in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J] in
/-- **Realised cumulative payoff** along a play sequence on `A`. -/
noncomputable def MatrixGame.realisedCumPayoff (A : MatrixGame I J ℝ) (iSeq : ℕ → I)
    (jSeq : ℕ → J) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range n, A.g (iSeq p) (jSeq p)
