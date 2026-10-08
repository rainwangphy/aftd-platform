import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.optimalColumnSet_convex

Topic: equilibria   Node: f21975275521

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimalColumnSet_convex`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.optimalColumnSet_convex
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
theorem MatrixGame.optimalColumnSet_convex : Convex ℝ A.optimalColumnSet := by
  apply Convex.inter (convex_stdSimplex ℝ J)
  apply convex_iInter
  intro i
  intro f hf g hg a b ha hb hab
  show ∑ j, (a • f + b • g) j * A.g i j ≤ A.value
  have hf' : ∑ j, f j * A.g i j ≤ A.value := hf
  have hg' : ∑ j, g j * A.g i j ≤ A.value := hg
  have hexpand : ∑ j, (a • f + b • g) j * A.g i j =
      a * (∑ j, f j * A.g i j) + b * (∑ j, g j * A.g i j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  calc a * (∑ j, f j * A.g i j) + b * (∑ j, g j * A.g i j)
      ≤ a * A.value + b * A.value := by gcongr
    _ = (a + b) * A.value := by ring
    _ = A.value := by rw [hab]; ring
