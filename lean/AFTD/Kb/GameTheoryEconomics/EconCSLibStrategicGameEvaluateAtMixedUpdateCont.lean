import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameEvaluateAtMixed
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.evaluate_at_mixed_update_cont

Topic: equilibria   Node: f31abdd609d9

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.evaluate_at_mixed_update_cont`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`σ ↦ evaluate_at_mixed G i (update σ i (stdSimplex.pure a))` is continuous.
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
/-- `σ ↦ evaluate_at_mixed G i (update σ i (stdSimplex.pure a))` is continuous. -/
lemma EconCSLib.StrategicGame.evaluate_at_mixed_update_cont (i : N) (a : G.strategy i) :
    Continuous (fun σ : MixedS G =>
      evaluate_at_mixed G i (update σ i (stdSimplex.pure a))) := by
  unfold evaluate_at_mixed
  apply continuous_finset_sum
  intro s _
  apply Continuous.mul _ continuous_const
  apply continuous_finset_prod
  intro j _
  by_cases h : j = i
  · subst h
    simp only [Function.update_self]
    exact continuous_const
  · simp only [ne_eq, h, not_false_eq_true, Function.update_of_ne]
    have h1 : Continuous (fun σ : MixedS G => σ j) := continuous_apply j
    have h2 : Continuous (fun x : stdSimplex ℝ (G.strategy j) => x.val (s j)) :=
      (continuous_apply (s j)).comp continuous_subtype_val
    exact h2.comp h1
