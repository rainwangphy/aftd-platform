import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLam0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAuxBddAbove
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxBddAbove

/-!
# MinimaxLoomis.lam.aux.le_lam0

Topic: equilibria   Node: 1ff4815f057d

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.lam.aux.le_lam0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The supremum `lam0` dominates every `lam.aux` value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- The supremum `lam0` dominates every `lam.aux` value. -/
theorem MinimaxLoomis.lam.aux.le_lam0 (A : I → J → ℝ) (x : stdSimplex ℝ I) :
    lam.aux A x ≤ lam0 A :=
  le_ciSup (bddAbove_def.2 (by
    obtain ⟨C, hC⟩ := lam.aux.bddAbove A
    exact ⟨C, by rintro r ⟨x, rfl⟩; exact hC x⟩)) x
