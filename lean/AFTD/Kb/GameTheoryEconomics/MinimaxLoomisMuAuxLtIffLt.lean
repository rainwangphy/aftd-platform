import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.mu.aux_lt_iff_lt

Topic: equilibria   Node: 1dda9a11dbe9

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.mu.aux_lt_iff_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`mu.aux A y < c` iff every pure-row expected payoff is below `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `mu.aux A y < c` iff every pure-row expected payoff is below `c`. -/
theorem MinimaxLoomis.mu.aux_lt_iff_lt (A : I → J → ℝ) (c : ℝ) (y : stdSimplex ℝ J) :
    mu.aux A y < c ↔ ∀ i, wsum y (fun j => A i j) < c := by
  simp [mu.aux, Finset.sup'_lt_iff]
