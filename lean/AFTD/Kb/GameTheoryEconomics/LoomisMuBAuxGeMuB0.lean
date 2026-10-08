import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxBddBelow
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.muB.aux.ge_muB0

Topic: equilibria   Node: 605ae23cb072

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.muB.aux.ge_muB0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every `muB.aux` value dominates the infimum `muB0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Every `muB.aux` value dominates the infimum `muB0`. -/
theorem Loomis.muB.aux.ge_muB0 {A B : I → J → ℝ} (hB : IsPositive B)
    (y : stdSimplex ℝ J) :
    muB0 A B ≤ muB.aux A B y :=
  ciInf_le (bddBelow_def.2 (by
    obtain ⟨C, hC⟩ := muB.aux.bddBelow hB
    exact ⟨C, by rintro r ⟨y, rfl⟩; exact hC y⟩)) y
