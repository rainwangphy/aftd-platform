import AFTD.Prelude

/-!
# FiniteImperfectGame

Topic: equilibria   Node: 755abac1f056

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 4 verbatim; compiled here.

Finite imperfect-information extensive game data. `info s = none` means the state is not in a strategic information set, typically because it is terminal or chance-controlled. `info s = some k` places state `s` in information set `k`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Finite imperfect-information extensive game data. `info s = none` means the state is not in a strategic information set, typically because it is terminal or chance-controlled. `info s = some k` places state `s` in information set `k`. -/
structure FiniteImperfectGame (N U : Type*) where
  State : Type*
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  InfoSet : Type*
  [infoDecidableEq : DecidableEq InfoSet]
  Action : State → Type*
  next : (s : State) → Action s → State
  init : State
  mover : State → Option N
  info : State → Option InfoSet
  payoff : State → N → U

attribute [instance] FiniteImperfectGame.stateFintype

attribute [instance] FiniteImperfectGame.stateDecidableEq

attribute [instance] FiniteImperfectGame.infoDecidableEq
