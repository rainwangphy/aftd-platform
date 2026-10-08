import AFTD.Prelude

/-!
# GameTree

Topic: equilibria   Node: dbd47074de0c

Provenance: formalization of a published result. Source: EconCSLib, `GameTree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite extensive-form game of perfect information, without chance. * `Leaf payoff` — a terminal state with a payoff vector `N → U`. * `Node mover head tail` — a decision node owned by `mover`, with non-empty children `head :: tail`. Finiteness is built into the inductive type; non-emptiness of children is built into the `Node` constructor via `head + tail`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A finite extensive-form game of perfect information, without chance. * `Leaf payoff` — a terminal state with a payoff vector `N → U`. * `Node mover head tail` — a decision node owned by `mover`, with non-empty children `head :: tail`. Finiteness is built into the inductive type; non-emptiness of children is built into the `Node` constructor via `head + tail`. -/
inductive GameTree (N : Type*) (U : Type*) : Type _ | Leaf (payoff : N → U) : GameTree N U
  | Node (mover : N) (head : GameTree N U) (tail : List (GameTree N U)) :
      GameTree N U
