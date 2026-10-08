import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLam0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMu0
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExistsXxLam0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExistsYyMu0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisE
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.Optimization.GeIffSimplexGe
import AFTD.Kb.Optimization.LeIffSimplexLe
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.lam0_le_mu0

Topic: equilibria   Node: cbecb65d10ae

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.lam0_le_mu0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weak duality for the two-player zero-sum matrix game: every maxmin value is bounded by every minmax value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Weak duality for the two-player zero-sum matrix game: every maxmin value is bounded by every minmax value. -/
theorem MinimaxLoomis.lam0_le_mu0 (A : I → J → ℝ) : lam0 A ≤ mu0 A := by
  obtain ⟨xx, Hxx⟩ := exists_xx_lam0 A
  obtain ⟨yy, Hyy⟩ := exists_yy_mu0 A
  calc lam0 A
      ≤ E A xx yy := by
        rw [E, wsum_wsum_comm]
        exact (ge_iff_simplex_ge.mp Hxx) yy
    _ ≤ mu0 A := by
        rw [E]
        exact (le_iff_simplex_le.mp Hyy) xx
