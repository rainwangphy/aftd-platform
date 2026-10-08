import AFTD.Prelude

/-!
# ZeroSumChance.Select

Topic: equilibria   Node: 693d4400590a

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.Select`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A binary choice: `l` = left branch, `r` = right branch.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A binary choice: `l` = left branch, `r` = right branch. -/
inductive ZeroSumChance.Select | l : Select  -- left
  | r : Select  -- right
  deriving Repr, DecidableEq
