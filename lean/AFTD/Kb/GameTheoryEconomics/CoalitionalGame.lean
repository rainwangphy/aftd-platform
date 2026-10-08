import AFTD.Prelude

/-!
# CoalitionalGame

Topic: general_equilibrium   Node: e1e26200aa0f

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A coalitional game with transferable utility. `N` is the player type; `U` is the utility type. `v` assigns a worth to each coalition, with the empty coalition worth zero. [MSZ 16.1] No finiteness or concrete number-system assumptions are baked in. Specialize `U` to `ℝ` only where real arithmetic is genuinely required.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
/-- A coalitional game with transferable utility. `N` is the player type; `U` is the utility type. `v` assigns a worth to each coalition, with the empty coalition worth zero. [MSZ 16.1] No finiteness or concrete number-system assumptions are baked in. Specialize `U` to `ℝ` only where real arithmetic is genuinely required. -/
structure CoalitionalGame (N : Type*) (U : Type*) [DecidableEq N] [AddZeroClass U] where
  /-- The characteristic function: worth of each coalition. -/
  v : Finset N → U
  /-- The empty coalition is worth zero. -/
  empty_zero : v ∅ = 0
