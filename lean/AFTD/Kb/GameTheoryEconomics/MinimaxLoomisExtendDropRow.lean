import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropColumn

/-!
# MinimaxLoomis.extendDropRow

Topic: equilibria   Node: 1d2aa0eae34e

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.extendDropRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dual: extend a mixed strategy on `I' = {i // i ≠ i₀}` to one on `I`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Dual: extend a mixed strategy on `I' = {i // i ≠ i₀}` to one on `I`. -/
noncomputable def MinimaxLoomis.extendDropRow [DecidableEq I] (i₀ : I)
    (x' : stdSimplex ℝ {i : I // i ≠ i₀}) :
    stdSimplex ℝ I :=
  extendDropColumn (J := I) i₀ x'
