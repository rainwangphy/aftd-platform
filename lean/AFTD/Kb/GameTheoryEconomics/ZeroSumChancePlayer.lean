import AFTD.Prelude

/-!
# ZeroSumChance.Player

Topic: equilibria   Node: 946030512831

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.Player`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The two players in a zero-sum game: A is the maximizer, B is the minimizer.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The two players in a zero-sum game: A is the maximizer, B is the minimizer. -/
inductive ZeroSumChance.Player | A : Player  -- Alice, maximizer
  | B : Player  -- Bob, minimizer
  deriving Repr, DecidableEq
