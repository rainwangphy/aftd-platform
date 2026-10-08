import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameEEqWsumWsum
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumLeWsum
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsMixedNashEq
import AFTD.Kb.GameTheoryEconomics.MatrixGameEEqWsumWsumSwap
import AFTD.Kb.Optimization.WsumConst

/-!
# MatrixGame.isMixedNashEq_of_pure

Topic: equilibria   Node: 653aa376d2e3

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.isMixedNashEq_of_pure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Pure-strategy guarantees give a mixed Nash equilibrium.** If `xx` guarantees value `v` against every pure column and `yy` caps the row player's payoff at `v` against every pure row, then `(xx, yy)` is a saddle-point mixed Nash equilibrium. Field-generic — only the saddle inequalities are used (no order-completeness).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Pure-strategy guarantees give a mixed Nash equilibrium.** If `xx` guarantees value `v` against every pure column and `yy` caps the row player's payoff at `v` against every pure row, then `(xx, yy)` is a saddle-point mixed Nash equilibrium. Field-generic — only the saddle inequalities are used (no order-completeness). -/
theorem MatrixGame.isMixedNashEq_of_pure {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (A : MatrixGame I J 𝕜)
    {xx : stdSimplex 𝕜 I} {yy : stdSimplex 𝕜 J} {v : 𝕜}
    (Hxx : ∀ j, v ≤ wsum xx (fun i => A.g i j))
    (Hyy : ∀ i, wsum yy (A.g i) ≤ v) :
    A.IsMixedNashEq xx yy := by
  refine ⟨?_, ?_⟩
  · -- Row player cannot improve: `A.E x' yy ≤ v ≤ A.E xx yy`.
    intro x'
    have hE_x'_le : A.E x' yy ≤ v := by
      rw [E_eq_wsum_wsum]
      calc wsum x' (fun i => wsum yy (A.g i))
          ≤ wsum x' (fun _ => v) := wsum_le_wsum x' Hyy
        _ = v := wsum_const x' v
    have hE_xx_ge : v ≤ A.E xx yy := by
      rw [E_eq_wsum_wsum_swap]
      calc v = wsum yy (fun _ => v) := (wsum_const yy v).symm
        _ ≤ wsum yy (fun j => wsum xx (fun i => A.g i j)) := wsum_le_wsum yy Hxx
    linarith
  · -- Column player cannot improve: `A.E xx yy ≤ v ≤ A.E xx y'`.
    intro y'
    have hE_xx_le : A.E xx yy ≤ v := by
      rw [E_eq_wsum_wsum]
      calc wsum xx (fun i => wsum yy (A.g i))
          ≤ wsum xx (fun _ => v) := wsum_le_wsum xx Hyy
        _ = v := wsum_const xx v
    have hE_xx_y'_ge : v ≤ A.E xx y' := by
      rw [E_eq_wsum_wsum_swap]
      calc v = wsum y' (fun _ => v) := (wsum_const y' v).symm
        _ ≤ wsum y' (fun j => wsum xx (fun i => A.g i j)) := wsum_le_wsum y' Hxx
    linarith
