import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame

Topic: equilibria   Node: d0404bfd4722

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A strategic game (normal-form game) with players `N` and utilities in `U`. The structure records only the bare data: strategy spaces and a payoff function. All assumptions (finiteness, ordering, computability) are added at usage sites.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A strategic game (normal-form game) with players `N` and utilities in `U`. The structure records only the bare data: strategy spaces and a payoff function. All assumptions (finiteness, ordering, computability) are added at usage sites. -/
structure EconCSLib.StrategicGame (N : Type*) (U : Type*) where
  /-- The strategy space of each player. -/
  strategy : N → Type*
  /-- The payoff function: maps a strategy profile to each player's utility. -/
  payoff : (∀ i, strategy i) → N → U
