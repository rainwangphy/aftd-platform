import AFTD.Prelude

/-!
# Examples.ImperfectInformation.P1Action

Topic: equilibria   Node: 999976b1b705

Provenance: formalization of a published result. Source: EconCSLib, `Examples.ImperfectInformation.P1Action`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Examples.ImperfectInformation.P1Action
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
inductive Examples.ImperfectInformation.P1Action | Stop
  deriving DecidableEq
