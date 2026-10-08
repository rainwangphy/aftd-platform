import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGamePayoffVector
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameCore
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsImputation
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsEfficient
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameCoalitionPayoff
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsIndividuallyRational

/-!
# CoalitionalGame.core_subset_imputations

Topic: general_equilibrium   Node: cfb025244a9f

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.core_subset_imputations`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Core.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every element of the core is an imputation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- Every element of the core is an imputation. -/
theorem CoalitionalGame.core_subset_imputations :
    G.Core ⊆ { x | G.IsImputation x } := by
  intro x ⟨heff, hcoal⟩
  refine ⟨heff, fun i => ?_⟩
  have h := hcoal {i}
  simp [coalitionPayoff] at h
  exact h
