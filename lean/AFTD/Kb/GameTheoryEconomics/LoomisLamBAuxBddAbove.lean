import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxContinuous
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB.aux.bddAbove

Topic: equilibria   Node: e7e2a63c4f9a

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB.aux.bddAbove`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`lamB.aux A B` is bounded above on the simplex (continuous function on a compact set).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `lamB.aux A B` is bounded above on the simplex (continuous function on a compact set). -/
theorem Loomis.lamB.aux.bddAbove {A B : I → J → ℝ} (hB : IsPositive B) :
    ∃ C, ∀ x, lamB.aux A B x ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ.image (lamB.aux.continuous hB)).bddAbove
  refine ⟨C, fun x => hC ⟨x, Set.mem_univ _, rfl⟩⟩
