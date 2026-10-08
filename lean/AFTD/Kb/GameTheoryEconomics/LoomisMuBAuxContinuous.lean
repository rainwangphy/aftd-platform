import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatio
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatioContinuous
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.muB.aux.continuous

Topic: equilibria   Node: 953b94b4ee55

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.muB.aux.continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`muB.aux A B` is continuous on the simplex.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `muB.aux A B` is continuous on the simplex. -/
theorem Loomis.muB.aux.continuous {A B : I → J → ℝ} (hB : IsPositive B) :
    Continuous (muB.aux A B) := by
  refine Continuous.finset_sup'_apply Finset.univ_nonempty ?_
  intro i _
  exact rowRatio.continuous hB i
