import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxContinuous
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatio
import AFTD.Kb.GameTheoryEconomics.LoomisByPos
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.exists_yy_muB0

Topic: equilibria   Node: e36086435bce

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.exists_yy_muB0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Attainment of `muB0`: there exists a mixed strategy `yy` with `(Ay yy)_i ≤ muB0 · (By yy)_i` for every row.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Attainment of `muB0`: there exists a mixed strategy `yy` with `(Ay yy)_i ≤ muB0 · (By yy)_i` for every row. -/
theorem Loomis.exists_yy_muB0 (A B : I → J → ℝ) (hB : IsPositive B) :
    ∃ yy : stdSimplex ℝ J, ∀ i, Ay A yy i ≤ muB0 A B * By B yy i := by
  obtain ⟨yy, _, hyy⟩ :=
    isCompact_univ.exists_isMinOn (α := ℝ) (β := stdSimplex ℝ J)
      Set.univ_nonempty (muB.aux.continuous hB).continuousOn
  rw [isMinOn_iff] at hyy
  refine ⟨yy, fun i => ?_⟩
  have h1 : muB.aux A B yy ≤ muB0 A B :=
    le_ciInf fun z => hyy z (Set.mem_univ _)
  have h2 : rowRatio A B yy i ≤ muB.aux A B yy :=
    Finset.le_sup' (f := fun i => rowRatio A B yy i) (Finset.mem_univ i)
  have hyyB : 0 < By B yy i := By_pos hB yy i
  have hratio : rowRatio A B yy i ≤ muB0 A B := h2.trans h1
  unfold rowRatio at hratio
  exact (div_le_iff₀ hyyB).mp hratio
