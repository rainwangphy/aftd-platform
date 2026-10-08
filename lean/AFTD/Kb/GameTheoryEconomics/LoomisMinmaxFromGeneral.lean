import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLam0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMu0
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisLoomisValueEq
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositiveOne
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0One
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0One
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.minmax_from_general

Topic: equilibria   Node: 54f4d6610973

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.minmax_from_general`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Simplified Loomis as a corollary** of the general theorem: the finite von Neumann minimax `MinimaxLoomis.lam0 A = MinimaxLoomis.mu0 A` follows by instantiating `loomis_value_eq` at the all-ones matrix `B = 𝟙`. This is the canonical "B = 𝟙 specialisation" route recorded by the [[minimax_from_loomis]] blueprint node, and the **sole** route to the finite von Neumann minimax: `MinimaxLoomis` keeps only the shared foundational layer (aggregates, attainment, weak duality, drop/extend infra), and its scalar equality is exported here rather than re-proved by a standalone induction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Loomis in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- **Simplified Loomis as a corollary** of the general theorem: the finite von Neumann minimax `MinimaxLoomis.lam0 A = MinimaxLoomis.mu0 A` follows by instantiating `loomis_value_eq` at the all-ones matrix `B = 𝟙`. This is the canonical "B = 𝟙 specialisation" route recorded by the [[minimax_from_loomis]] blueprint node, and the **sole** route to the finite von Neumann minimax: `MinimaxLoomis` keeps only the shared foundational layer (aggregates, attainment, weak duality, drop/extend infra), and its scalar equality is exported here rather than re-proved by a standalone induction. -/
theorem Loomis.minmax_from_general (A : I → J → ℝ) :
    MinimaxLoomis.lam0 A = MinimaxLoomis.mu0 A := by
  have h := loomis_value_eq A (fun _ _ => 1) IsPositive.one
  rw [lamB0_one, muB0_one] at h
  exact h
