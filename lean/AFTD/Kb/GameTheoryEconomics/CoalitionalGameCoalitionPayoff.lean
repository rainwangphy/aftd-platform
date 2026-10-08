import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGamePayoffVector
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.coalitionPayoff

Topic: general_equilibrium   Node: e9f4ce588353

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.coalitionPayoff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The total payoff of a coalition under a payoff vector. Requires `[AddCommMonoid U]` for the finite sum.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- The total payoff of a coalition under a payoff vector. Requires `[AddCommMonoid U]` for the finite sum. -/
def CoalitionalGame.coalitionPayoff [AddCommMonoid U] (x : PayoffVector N U) (S : Finset N) : U :=
  ∑ i ∈ S, x i
