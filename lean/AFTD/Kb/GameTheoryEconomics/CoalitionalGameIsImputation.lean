import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGamePayoffVector
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsEfficient
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsIndividuallyRational

/-!
# CoalitionalGame.IsImputation

Topic: general_equilibrium   Node: 71f09b388814

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsImputation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An imputation is an efficient and individually rational payoff vector. [MSZ 17.1]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- An imputation is an efficient and individually rational payoff vector. [MSZ 17.1] -/
def CoalitionalGame.IsImputation [Fintype N] [AddCommMonoid U] [LE U] (x : PayoffVector N U) : Prop :=
  G.IsEfficient x ∧ G.IsIndividuallyRational x
