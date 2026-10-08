import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameEmpiricalFrequency
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.IsFictitiousPlay

Topic: equilibria   Node: 909766e9b798

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsFictitiousPlay`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Learning/FictitiousPlay.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Fictitious play realisation** on a matrix game `A`. At every step `n + 1`, the row player picks a pure row best-responding to the column player's empirical frequency `y_n`, and dually for the column player. The `n = 0` "warm-up" step is unconstrained (the empirical frequency is undefined before any play has occurred).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J] in
/-- **Fictitious play realisation** on a matrix game `A`. At every step `n + 1`, the row player picks a pure row best-responding to the column player's empirical frequency `y_n`, and dually for the column player. The `n = 0` "warm-up" step is unconstrained (the empirical frequency is undefined before any play has occurred). -/
def MatrixGame.IsFictitiousPlay (A : MatrixGame I J ℝ) (iSeq : ℕ → I) (jSeq : ℕ → J) : Prop :=
  ∀ n : ℕ, 0 < n →
    (∀ k : I, A.Ei k (empiricalFrequency jSeq n) ≤ A.Ei (iSeq n) (empiricalFrequency jSeq n)) ∧
    (∀ ℓ : J, A.Ej (empiricalFrequency iSeq n) (jSeq n) ≤ A.Ej (empiricalFrequency iSeq n) ℓ)
