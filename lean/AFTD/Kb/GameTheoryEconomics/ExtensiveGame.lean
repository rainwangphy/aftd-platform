import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.Arena

/-!
# ExtensiveGame

Topic: equilibria   Node: eeac6de55856

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame`. Lean proof by xbei, Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state-payoff extensive game: a payoff-free controlled game together with a convenient endpoint-state payoff. * `mover s` = who controls state `s` (`none` = non-player-controlled) * `payoff s i` = payoff for player `i` at state `s` (meaningful at terminal states) General terminal-history, complete-path, and winning-condition semantics are separate objective layers; this field is not their authoritative definition. No `isTerminal` field — terminal states are detected by `IsEmpty (Action s)`. No proof terms to carry around.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A state-payoff extensive game: a payoff-free controlled game together with a convenient endpoint-state payoff. * `mover s` = who controls state `s` (`none` = non-player-controlled) * `payoff s i` = payoff for player `i` at state `s` (meaningful at terminal states) General terminal-history, complete-path, and winning-condition semantics are separate objective layers; this field is not their authoritative definition. No `isTerminal` field — terminal states are detected by `IsEmpty (Action s)`. No proof terms to carry around. -/
structure ExtensiveGame (N : Type*) (U : Type*) extends ControlledGame N where
  /-- Payoff at each state for each player.
      Meaningful at terminal states; may be arbitrary elsewhere. -/
  payoff : State → N → U
