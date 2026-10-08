import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsAntisymmetric
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsAntisymmetric.quadform_zero

Topic: equilibria   Node: 9dd29b0a93a0

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.IsAntisymmetric.quadform_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Antisymmetric.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For any vector `z`, `∑_{i,j} z_i B_{ij} z_j = 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- For any vector `z`, `∑_{i,j} z_i B_{ij} z_j = 0`. -/
theorem EconCSLib.StrategicGame.IsAntisymmetric.quadform_zero {B : I → I → ℝ} (hB : IsAntisymmetric B)
    (z : I → ℝ) : ∑ i, ∑ j, z i * B i j * z j = 0 := by
  -- Strategy: set S = LHS, compute T = ∑_i ∑_j z_j B_ji z_i in two ways.
  -- (1) T = S by sum_comm + alpha-rename + ring.
  -- (2) T = -S by antisymmetry B_ji = -B_ij.
  -- Conclude 2 * S = 0.
  set S : ℝ := ∑ i, ∑ j, z i * B i j * z j with hS_def
  have hT_eq_S : (∑ i, ∑ j, z j * B j i * z i) = S := by
    rw [hS_def, Finset.sum_comm]
  have hT_eq_negS : (∑ i, ∑ j, z j * B j i * z i) = -S := by
    have step1 : (∑ i, ∑ j, z j * B j i * z i) = ∑ i, ∑ j, -(z i * B i j * z j) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hB j i]; ring
    rw [step1]
    rw [show (∑ i, ∑ j, -(z i * B i j * z j))
          = ∑ i, -(∑ j, z i * B i j * z j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_neg_distrib _)]
    rw [Finset.sum_neg_distrib]
  linarith [hT_eq_S, hT_eq_negS]
