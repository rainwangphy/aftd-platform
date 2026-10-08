import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxContinuous
import AFTD.Kb.GameTheoryEconomics.LoomisColRatio
import AFTD.Kb.GameTheoryEconomics.LoomisXBPos
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.exists_xx_lamB0

Topic: equilibria   Node: 0399a8a40826

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.exists_xx_lamB0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Attainment of `lamB0`: there exists a mixed strategy `xx` with `(xA xx)_j ≥ lamB0 · (xB xx)_j` for every column.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Attainment of `lamB0`: there exists a mixed strategy `xx` with `(xA xx)_j ≥ lamB0 · (xB xx)_j` for every column. -/
theorem Loomis.exists_xx_lamB0 (A B : I → J → ℝ) (hB : IsPositive B) :
    ∃ xx : stdSimplex ℝ I, ∀ j, lamB0 A B * xB B xx j ≤ xA A xx j := by
  obtain ⟨xx, _, hxx⟩ :=
    isCompact_univ.exists_isMaxOn (α := ℝ) (β := stdSimplex ℝ I)
      Set.univ_nonempty (lamB.aux.continuous hB).continuousOn
  rw [isMaxOn_iff] at hxx
  refine ⟨xx, fun j => ?_⟩
  have h1 : lamB0 A B ≤ lamB.aux A B xx :=
    ciSup_le fun y => hxx y (Set.mem_univ _)
  have h2 : lamB.aux A B xx ≤ colRatio A B xx j :=
    Finset.inf'_le _ (Finset.mem_univ j)
  have hxxB : 0 < xB B xx j := xB_pos hB xx j
  -- lamB0 ≤ xA / xB ⇒ lamB0 * xB ≤ xA  (since xB > 0)
  have hratio : lamB0 A B ≤ colRatio A B xx j := h1.trans h2
  unfold colRatio at hratio
  exact (le_div_iff₀ hxxB).mp hratio
