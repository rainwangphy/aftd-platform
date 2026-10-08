import AFTD.Prelude

/-!
# Arena

Topic: equilibria   Node: 1c3aab0a5446

Provenance: formalization of a published result. Source: EconCSLib, `Arena`. Lean proof by Lazyfill (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A game arena: the pure dynamics of an extensive-form game. States, actions, and transitions are stored without players, payoffs, or probability. A state is terminal iff `Action s` is empty.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A game arena: the pure dynamics of an extensive-form game. States, actions, and transitions are stored without players, payoffs, or probability. A state is terminal iff `Action s` is empty. -/
structure Arena where
  /-- The state space. -/
  State : Type*
  /-- Available actions at each state. Empty means terminal. -/
  Action : State → Type*
  /-- Transition function from a state and one legal action. -/
  next : (s : State) → Action s → State
