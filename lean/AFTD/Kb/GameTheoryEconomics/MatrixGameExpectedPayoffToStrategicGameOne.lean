import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.MatrixGameToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumExpectedPayoffAddZero
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameExpectedPayoff
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.expectedPayoff_toStrategicGame_one

Topic: equilibria   Node: a703324d587a

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.expectedPayoff_toStrategicGame_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Mirror: `expectedPayoff A.toStrategicGame p 1 = -(A.E (p 0) (p 1))`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
variable [DecidableEq I] [DecidableEq J] in
/-- Mirror: `expectedPayoff A.toStrategicGame p 1 = -(A.E (p 0) (p 1))`. -/
theorem MatrixGame.expectedPayoff_toStrategicGame_one {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (p : EconCSLib.StrategicGame.MixedProfile A.toStrategicGame) :
    EconCSLib.StrategicGame.expectedPayoff A.toStrategicGame p 1
      = -(A.E (p 0) (p 1)) := by
  let double : 𝕜 := ∑ i : I, ∑ j : J, (p 0).val i * (p 1).val j * A.g i j
  have hLHS : EconCSLib.StrategicGame.expectedPayoff A.toStrategicGame p 1 = -double := by
    unfold EconCSLib.StrategicGame.expectedPayoff
    rw [show
          (∑ σ : (∀ i : Fin 2, A.toStrategicGame.strategy i),
              (∏ i : Fin 2, (p i).val (σ i)) * A.toStrategicGame.payoff σ 1)
          = ∑ ij : I × J, -((p 0).val ij.1 * (p 1).val ij.2 * A.g ij.1 ij.2)
        from ?_]
    · rw [Finset.sum_neg_distrib, Fintype.sum_prod_type]
    · apply Fintype.sum_equiv (piFinTwoEquiv A.toStrategicGame.strategy)
      intro σ
      rw [Fin.prod_univ_two]
      -- Unfold `payoff σ 1 = -(A.g (σ 0) (σ 1))` and use ring.
      show ((p 0).val (σ 0) * (p 1).val (σ 1)) * (-(A.g (σ 0) (σ 1)))
         = -((p 0).val (σ 0) * (p 1).val (σ 1) * A.g (σ 0) (σ 1))
      ring
  have hRHS : A.E (p 0) (p 1) = double := by
    change (∑ i, (p 0).val i * (∑ j, (p 1).val j * A.g i j)) = double
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hLHS, hRHS]
