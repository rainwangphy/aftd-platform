import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropColumn
import AFTD.Kb.GameTheoryEconomics.LoomisDropCol
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisWsumExtendDropColumn
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.Ay_extendDropColumn

Topic: equilibria   Node: e4a39b6d1c9e

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.Ay_extendDropColumn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extending `y' ∈ Δ(J')` to `Δ(J)` by zero at `j₀` recovers the same row aggregates from `A` (and `B`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Extending `y' ∈ Δ(J')` to `Δ(J)` by zero at `j₀` recovers the same row aggregates from `A` (and `B`). -/
theorem Loomis.Ay_extendDropColumn [DecidableEq J] (i : I) (A : I → J → ℝ)
    (j₀ : J) (y' : stdSimplex ℝ {j : J // j ≠ j₀}) :
    Ay A (MinimaxLoomis.extendDropColumn j₀ y') i = Ay (dropCol A j₀) y' i := by
  unfold Ay
  rw [MinimaxLoomis.wsum_extendDropColumn]
  rfl
