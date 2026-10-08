import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameEvaluateAtMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.evaluate_at_mixed_cont

Topic: equilibria   Node: 63d43bffb1bf

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.evaluate_at_mixed_cont`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`evaluate_at_mixed G i` is continuous in the mixed profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Function in
set_option linter.unusedSectionVars false in
variable {N : Type*} in
variable (G : EconCSLib.StrategicGame N ℝ) in
variable [Fintype N] [DecidableEq N] in
variable [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)] in
variable [∀ i, Inhabited (G.strategy i)] in
/-- `evaluate_at_mixed G i` is continuous in the mixed profile. -/
lemma EconCSLib.StrategicGame.evaluate_at_mixed_cont (i : N) :
    Continuous (fun σ : MixedS G => evaluate_at_mixed G i σ) := by
  unfold evaluate_at_mixed
  apply continuous_finset_sum
  intro s _
  apply Continuous.mul _ continuous_const
  apply continuous_finset_prod
  intro j _
  have h1 : Continuous (fun σ : MixedS G => σ j) := continuous_apply j
  have h2 : Continuous (fun x : stdSimplex ℝ (G.strategy j) => x.val (s j)) :=
    (continuous_apply (s j)).comp continuous_subtype_val
  exact h2.comp h1
