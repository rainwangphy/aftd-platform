import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropRow
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisWsumExtendDropColumn
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.wsum_extendDropRow

Topic: equilibria   Node: 4018ff5ed4c7

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.wsum_extendDropRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Companion for row extension.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Companion for row extension. -/
theorem MinimaxLoomis.wsum_extendDropRow [DecidableEq I] (i₀ : I)
    (x' : stdSimplex ℝ {i : I // i ≠ i₀}) (f : I → ℝ) :
    wsum (extendDropRow i₀ x') f
      = ∑ i' : {i : I // i ≠ i₀}, x'.val i' * f i'.val :=
  wsum_extendDropColumn (J := I) i₀ x' f
