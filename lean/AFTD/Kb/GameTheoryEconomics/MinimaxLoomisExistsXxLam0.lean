import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLam0
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAuxContinuous
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxContinuous
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxContinuous

/-!
# MinimaxLoomis.exists_xx_lam0

Topic: equilibria   Node: 521e11f4eb49

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.exists_xx_lam0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There exists a mixed strategy `xx` whose column-payoffs all dominate `lam0 A`. Compactness + continuity gives a maximiser of `lam.aux`; that maximiser realises the supremum and beats every pure-column expectation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- There exists a mixed strategy `xx` whose column-payoffs all dominate `lam0 A`. Compactness + continuity gives a maximiser of `lam.aux`; that maximiser realises the supremum and beats every pure-column expectation. -/
theorem MinimaxLoomis.exists_xx_lam0 (A : I → J → ℝ) :
    ∃ xx : stdSimplex ℝ I, ∀ j, lam0 A ≤ wsum xx (fun i => A i j) := by
  obtain ⟨xx, _, hxx⟩ :=
    isCompact_univ.exists_isMaxOn (α := ℝ) (β := stdSimplex ℝ I)
      Set.univ_nonempty (lam.aux.continuous A).continuousOn
  rw [isMaxOn_iff] at hxx
  refine ⟨xx, fun j => ?_⟩
  have h1 : lam0 A ≤ lam.aux A xx := ciSup_le fun y => hxx y (Set.mem_univ _)
  have h2 : lam.aux A xx ≤ wsum xx (fun i => A i j) :=
    Finset.inf'_le _ (Finset.mem_univ j)
  exact h1.trans h2
