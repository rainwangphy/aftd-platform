import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxMinimax
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsMixedNashEqOfPure
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsMixedNashEq

/-!
# MatrixGame.exists_mixed_nash_equilibrium

Topic: equilibria   Node: 7c3b7b225f34

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.exists_mixed_nash_equilibrium`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Matrix games have a mixed Nash equilibrium — over any linearly ordered field.** Packages the field-generic saddle `Minimax.minimax` (proved by von Neumann symmetrisation; no compactness, no order-completeness) into the `IsMixedNashEq` saddle-point form. The ℝ case is the `𝕜 := ℝ` instance, so all ℝ consumers are unaffected.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Matrix games have a mixed Nash equilibrium — over any linearly ordered field.** Packages the field-generic saddle `Minimax.minimax` (proved by von Neumann symmetrisation; no compactness, no order-completeness) into the `IsMixedNashEq` saddle-point form. The ℝ case is the `𝕜 := ℝ` instance, so all ℝ consumers are unaffected. -/
theorem MatrixGame.exists_mixed_nash_equilibrium {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (A : MatrixGame I J 𝕜) :
    ∃ (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J), A.IsMixedNashEq xx yy := by
  classical
  obtain ⟨x, y, v, hx_nn, hx_sum, hy_nn, hy_sum, hxA, hAy⟩ := Minimax.minimax A.g
  refine ⟨⟨x, hx_nn, hx_sum⟩, ⟨y, hy_nn, hy_sum⟩, ?_⟩
  apply isMixedNashEq_of_pure A (v := v)
  · intro j; exact hxA j
  · intro i
    show (∑ j, y j * A.g i j) ≤ v
    calc (∑ j, y j * A.g i j) = ∑ j, A.g i j * y j :=
          Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ ≤ v := hAy i
