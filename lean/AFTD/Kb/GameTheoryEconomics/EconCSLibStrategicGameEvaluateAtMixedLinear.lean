import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedS
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameEvaluateAtMixed
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.evaluate_at_mixed_linear

Topic: equilibria   Node: 9cab9b58c200

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.evaluate_at_mixed_linear`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Nash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`evaluate_at_mixed G i` is linear in the `i`-th mixed strategy: for any `τ : stdSimplex ℝ (G.strategy i)`, `evaluate_at_mixed G i (update σ i τ) = ∑ a, (τ.val a) * evaluate_at_mixed G i (update σ i (stdSimplex.pure a))`.
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
/-- `evaluate_at_mixed G i` is linear in the `i`-th mixed strategy: for any `τ : stdSimplex ℝ (G.strategy i)`, `evaluate_at_mixed G i (update σ i τ) = ∑ a, (τ.val a) * evaluate_at_mixed G i (update σ i (stdSimplex.pure a))`. -/
lemma EconCSLib.StrategicGame.evaluate_at_mixed_linear (i : N) (σ : MixedS G) (τ : stdSimplex ℝ (G.strategy i)) :
    evaluate_at_mixed G i (update σ i τ) =
      ∑ a : G.strategy i, (τ.val a) * evaluate_at_mixed G i (update σ i (stdSimplex.pure a)) := by
  simp only [evaluate_at_mixed, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext s
  -- Let P = ∏_{j≠i} σ_j(s_j) be the "other players" factor (independent of player i's strategy)
  set P := ∏ j ∈ Finset.univ.erase i, (σ j).val (s j) with hP_def
  -- The τ product factors as τ(s_i) * P
  have htau_prod : ∏ j : N, (update σ i τ j).val (s j) = τ.val (s i) * P := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [Function.update_self]
    · apply Finset.prod_congr rfl; intro j hj
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  -- The pure-strategy product factors as (if s_i = a then 1 else 0) * P
  have hpure_prod : ∀ a : G.strategy i,
      ∏ j : N, (update σ i (stdSimplex.pure a) j).val (s j) =
        (if s i = a then 1 else 0) * P := by
    intro a
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [Function.update_self, stdSimplex.pure_apply]
    · apply Finset.prod_congr rfl; intro j hj
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [htau_prod]
  simp_rw [hpure_prod]
  ring_nf
  simp [Finset.sum_ite_eq, Finset.mem_univ]
  ring
