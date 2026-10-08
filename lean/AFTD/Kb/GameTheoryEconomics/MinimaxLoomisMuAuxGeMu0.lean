import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMu0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAuxBddBelow
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxBddBelow

/-!
# MinimaxLoomis.mu.aux.ge_mu0

Topic: equilibria   Node: b64190aa865a

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.mu.aux.ge_mu0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The infimum `mu0` is dominated by every `mu.aux` value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- The infimum `mu0` is dominated by every `mu.aux` value. -/
theorem MinimaxLoomis.mu.aux.ge_mu0 (A : I → J → ℝ) (y : stdSimplex ℝ J) :
    mu0 A ≤ mu.aux A y :=
  ciInf_le (bddBelow_def.2 (by
    obtain ⟨C, hC⟩ := mu.aux.bddBelow A
    exact ⟨C, by rintro r ⟨y, rfl⟩; exact hC y⟩)) y
