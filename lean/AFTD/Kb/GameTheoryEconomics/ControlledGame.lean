import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Arena

/-!
# ControlledGame

Topic: equilibria   Node: 990006f1b3a6

Provenance: formalization of a published result. Source: EconCSLib, `ControlledGame`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A payoff-free controlled extensive-game skeleton. `ControlledGame` adds only a distinguished initial state and a mover label to the pure `Arena` dynamics. It deliberately stores no objective, payoff, probability law, finiteness, decidability, or information data. At a nonterminal state, `mover s = none` means only that the state is not controlled by a strategic player. It does not itself supply a chance distribution. The mover label at a terminal state is semantically ignored.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A payoff-free controlled extensive-game skeleton. `ControlledGame` adds only a distinguished initial state and a mover label to the pure `Arena` dynamics. It deliberately stores no objective, payoff, probability law, finiteness, decidability, or information data. At a nonterminal state, `mover s = none` means only that the state is not controlled by a strategic player. It does not itself supply a chance distribution. The mover label at a terminal state is semantically ignored. -/
structure ControlledGame (N : Type*) extends Arena where
  /-- The initial state (root of the controlled game). -/
  init : State
  /-- Who controls each state. `none` means non-player-controlled. -/
  mover : State → Option N
