import AFTD.Prelude

/-!
# StochasticGameTree

Topic: equilibria   Node: 63a3c0dd6366

Provenance: formalization of a published result. Source: EconCSLib, `StochasticGameTree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StochasticGameTree
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
inductive StochasticGameTree (N : Type*) : Type _ | Leaf (payoff : N → ℚ) : StochasticGameTree N
  | Player (mover : N) (head : StochasticGameTree N) (tail : List (StochasticGameTree N)) :
      StochasticGameTree N
  | Chance (headProb : ℚ) (head : StochasticGameTree N)
      (tail : List (ℚ × StochasticGameTree N)) : StochasticGameTree N
