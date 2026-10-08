import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsAntisymmetricQuadformZero
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsAntisymmetric

/-!
# EconCSLib.StrategicGame.antisymmetric_self_pairing_zero

Topic: equilibria   Node: c9eb8aaa7ae8

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.antisymmetric_self_pairing_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Antisymmetric.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`xᵀ B x = 0` for any mixed strategy `x` (when `B` is antisymmetric), where `xᵀ B x = ∑ i, xx_i * (∑ j, B_ij * xx_j)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- `xᵀ B x = 0` for any mixed strategy `x` (when `B` is antisymmetric), where `xᵀ B x = ∑ i, xx_i * (∑ j, B_ij * xx_j)`. -/
theorem EconCSLib.StrategicGame.antisymmetric_self_pairing_zero {B : I → I → ℝ}
    (hB : IsAntisymmetric B) (x : stdSimplex ℝ I) :
    ∑ i, x.val i * (∑ j, B i j * x.val j) = 0 := by
  have hsplit : (∑ i, x.val i * (∑ j, B i j * x.val j))
              = ∑ i, ∑ j, x.val i * B i j * x.val j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hsplit]
  exact hB.quadform_zero x.val
