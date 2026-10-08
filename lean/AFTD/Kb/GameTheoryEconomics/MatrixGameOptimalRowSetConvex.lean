import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.optimalRowSet_convex

Topic: equilibria   Node: b4ad51dd2d1d

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimalRowSet_convex`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.optimalRowSet_convex
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
theorem MatrixGame.optimalRowSet_convex : Convex ℝ A.optimalRowSet := by
  apply Convex.inter (convex_stdSimplex ℝ I)
  apply convex_iInter
  intro j
  -- Half-space {f | A.value ≤ ∑ i, f i * A.g i j} is convex.
  intro f hf g hg a b ha hb hab
  show A.value ≤ ∑ i, (a • f + b • g) i * A.g i j
  have hf' : A.value ≤ ∑ i, f i * A.g i j := hf
  have hg' : A.value ≤ ∑ i, g i * A.g i j := hg
  have hexpand : ∑ i, (a • f + b • g) i * A.g i j =
      a * (∑ i, f i * A.g i j) + b * (∑ i, g i * A.g i j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexpand]
  calc A.value
      = (a + b) * A.value := by rw [hab]; ring
    _ = a * A.value + b * A.value := by ring
    _ ≤ a * (∑ i, f i * A.g i j) + b * (∑ i, g i * A.g i j) := by gcongr
