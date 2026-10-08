import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMu0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAuxContinuous
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxContinuous
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxContinuous

/-!
# MinimaxLoomis.exists_yy_mu0

Topic: equilibria   Node: 606a90e5dbb9

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.exists_yy_mu0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There exists a mixed strategy `yy` whose row-payoffs are all dominated by `mu0 A`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- There exists a mixed strategy `yy` whose row-payoffs are all dominated by `mu0 A`. -/
theorem MinimaxLoomis.exists_yy_mu0 (A : I → J → ℝ) :
    ∃ yy : stdSimplex ℝ J, ∀ i, wsum yy (fun j => A i j) ≤ mu0 A := by
  obtain ⟨yy, _, hyy⟩ :=
    isCompact_univ.exists_isMinOn (α := ℝ) (β := stdSimplex ℝ J)
      Set.univ_nonempty (mu.aux.continuous A).continuousOn
  rw [isMinOn_iff] at hyy
  refine ⟨yy, fun i => ?_⟩
  have h1 : mu.aux A yy ≤ mu0 A := le_ciInf fun z => hyy z (Set.mem_univ _)
  have h2 : wsum yy (fun j => A i j) ≤ mu.aux A yy :=
    Finset.le_sup' (f := fun i => wsum yy (fun j => A i j)) (Finset.mem_univ i)
  exact h2.trans h1
