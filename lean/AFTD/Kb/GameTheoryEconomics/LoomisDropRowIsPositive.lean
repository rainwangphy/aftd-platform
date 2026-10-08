import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisDropRow

/-!
# Loomis.dropRow.IsPositive

Topic: equilibria   Node: 3577cda3afc2

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.dropRow.IsPositive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dropping a row preserves entrywise positivity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Dropping a row preserves entrywise positivity. -/
theorem Loomis.dropRow.IsPositive [DecidableEq I] {B : I → J → ℝ}
    (hB : IsPositive B) (i₀ : I) : IsPositive (dropRow B i₀) :=
  fun i' j => hB i'.val j
