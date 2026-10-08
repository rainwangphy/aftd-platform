import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.LoomisExistsXxLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisExistsYyMuB0
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisXByPos
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.GameTheoryEconomics.LoomisXBySwap
import AFTD.Kb.GameTheoryEconomics.LoomisWsumConstMul
import AFTD.Kb.Optimization.WsumLeWsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB0_le_muB0

Topic: equilibria   Node: 6f4022def20d

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB0_le_muB0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Weak duality** for the Loomis scalars: `lamB0 ≤ muB0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- **Weak duality** for the Loomis scalars: `lamB0 ≤ muB0`. -/
theorem Loomis.lamB0_le_muB0 (A B : I → J → ℝ) (hB : IsPositive B) :
    lamB0 A B ≤ muB0 A B := by
  obtain ⟨xx, Hxx⟩ := exists_xx_lamB0 A B hB
  obtain ⟨yy, Hyy⟩ := exists_yy_muB0 A B hB
  set xxByy : ℝ := wsum xx (fun i => By B yy i) with hxxByy_def
  have hxxByy_pos : 0 < xxByy := xBy_pos hB xx yy
  -- The pairing `xx A · yy`, written both ways.
  set pairing : ℝ := wsum xx (fun i => Ay A yy i) with hpairing_def
  have hswap : pairing = wsum yy (fun j => xA A xx j) := by
    rw [hpairing_def]
    unfold Ay xA
    exact wsum_wsum_comm xx yy A
  -- lamB0 · xxByy ≤ pairing
  have h_lam : lamB0 A B * xxByy ≤ pairing := by
    rw [hswap]
    calc lamB0 A B * xxByy
        = lamB0 A B * wsum yy (fun j => xB B xx j) := by
          rw [hxxByy_def, xBy_swap]
      _ = wsum yy (fun j => lamB0 A B * xB B xx j) := by
          rw [wsum_const_mul]
      _ ≤ wsum yy (fun j => xA A xx j) :=
          wsum_le_wsum yy (fun j => Hxx j)
  -- pairing ≤ muB0 · xxByy
  have h_mu : pairing ≤ muB0 A B * xxByy := by
    rw [hpairing_def]
    calc wsum xx (fun i => Ay A yy i)
        ≤ wsum xx (fun i => muB0 A B * By B yy i) :=
          wsum_le_wsum xx (fun i => Hyy i)
      _ = muB0 A B * wsum xx (fun i => By B yy i) := by
          rw [wsum_const_mul]
      _ = muB0 A B * xxByy := by rw [hxxByy_def]
  -- Combine and divide by the positive xxByy.
  have hcombo : lamB0 A B * xxByy ≤ muB0 A B * xxByy := h_lam.trans h_mu
  exact le_of_mul_le_mul_right hcombo hxxByy_pos
