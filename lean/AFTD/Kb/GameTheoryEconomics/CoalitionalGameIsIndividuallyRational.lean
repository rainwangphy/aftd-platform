import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGamePayoffVector

/-!
# CoalitionalGame.IsIndividuallyRational

Topic: general_equilibrium   Node: 79dc943b3686

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsIndividuallyRational`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A payoff vector is individually rational if each player gets at least their singleton worth. Requires `[LE U]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- A payoff vector is individually rational if each player gets at least their singleton worth. Requires `[LE U]`. -/
def CoalitionalGame.IsIndividuallyRational [LE U] (x : PayoffVector N U) : Prop :=
  ∀ i : N, x i ≥ G.v {i}
