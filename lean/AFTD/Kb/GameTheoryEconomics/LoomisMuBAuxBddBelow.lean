import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxContinuous
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.muB.aux.bddBelow

Topic: equilibria   Node: a6682c73bd21

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.muB.aux.bddBelow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`muB.aux A B` is bounded below on the simplex.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `muB.aux A B` is bounded below on the simplex. -/
theorem Loomis.muB.aux.bddBelow {A B : I → J → ℝ} (hB : IsPositive B) :
    ∃ C, ∀ y, C ≤ muB.aux A B y := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ.image (muB.aux.continuous hB)).bddBelow
  refine ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩
