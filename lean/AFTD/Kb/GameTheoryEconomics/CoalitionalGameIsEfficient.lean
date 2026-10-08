import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGamePayoffVector
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameCoalitionPayoff

/-!
# CoalitionalGame.IsEfficient

Topic: general_equilibrium   Node: 0250fe44977d

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsEfficient`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A payoff vector is efficient if it distributes exactly `v(N)`. [MSZ 16.1] Requires `[Fintype N]` and `[AddCommMonoid U]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- A payoff vector is efficient if it distributes exactly `v(N)`. [MSZ 16.1] Requires `[Fintype N]` and `[AddCommMonoid U]`. -/
def CoalitionalGame.IsEfficient [Fintype N] [AddCommMonoid U] (x : PayoffVector N U) : Prop :=
  coalitionPayoff x Finset.univ = G.v Finset.univ
