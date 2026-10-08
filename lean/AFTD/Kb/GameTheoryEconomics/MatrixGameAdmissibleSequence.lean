import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsFictitiousPlay

/-!
# MatrixGame.AdmissibleSequence

Topic: equilibria   Node: 436d99049ea8

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.AdmissibleSequence`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Learning/Robinson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An **admissible sequence** on a matrix game `A` (Robinson 1951 setup). Records cumulative counterfactual payoff vectors `α(t) : J → ℝ` (payoff to playing column `j` against the actual row sequence) and `β(t) : I → ℝ` (payoff to playing row `i` against the actual column sequence), together with the row/column choice sequences and the admissibility conditions: * `init_bracket` — `min_j α^j(0) = max_i β^i(0)` (the bracket-start condition, MFoGT (i)). * `iSeq_best`, `jSeq_best` — at each step the chosen row is in `argmax β(t)` and the chosen column is in `argmin α(t)`. * `α_step`, `β_step` — the cumulative-payoff update by the chosen pure actions, MFoGT (ii). This is the cumulative-payoff encoding of a fictitious-play realisation; see `MatrixGame.IsFictitiousPlay` for the empirical-frequency formulation, and the blueprint node for the correspondence `α(t)/t = x(t) A`, `β(t)/t = A y(t)` (plus the negligible boundary).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- An **admissible sequence** on a matrix game `A` (Robinson 1951 setup). Records cumulative counterfactual payoff vectors `α(t) : J → ℝ` (payoff to playing column `j` against the actual row sequence) and `β(t) : I → ℝ` (payoff to playing row `i` against the actual column sequence), together with the row/column choice sequences and the admissibility conditions: * `init_bracket` — `min_j α^j(0) = max_i β^i(0)` (the bracket-start condition, MFoGT (i)). * `iSeq_best`, `jSeq_best` — at each step the chosen row is in `argmax β(t)` and the chosen column is in `argmin α(t)`. * `α_step`, `β_step` — the cumulative-payoff update by the chosen pure actions, MFoGT (ii). This is the cumulative-payoff encoding of a fictitious-play realisation; see `MatrixGame.IsFictitiousPlay` for the empirical-frequency formulation, and the blueprint node for the correspondence `α(t)/t = x(t) A`, `β(t)/t = A y(t)` (plus the negligible boundary). -/
structure MatrixGame.AdmissibleSequence (A : MatrixGame I J ℝ) where
  α : ℕ → J → ℝ
  β : ℕ → I → ℝ
  iSeq : ℕ → I
  jSeq : ℕ → J
  init_bracket :
    Finset.univ.inf' Finset.univ_nonempty (α 0)
      = Finset.univ.sup' Finset.univ_nonempty (β 0)
  iSeq_best :
    ∀ t i', β t i' ≤ β t (iSeq t)
  jSeq_best :
    ∀ t j', α t (jSeq t) ≤ α t j'
  α_step :
    ∀ t j, α (t + 1) j = α t j + A.g (iSeq t) j
  β_step :
    ∀ t i, β (t + 1) i = β t i + A.g i (jSeq t)
