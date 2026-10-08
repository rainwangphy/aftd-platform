import AFTD.Prelude

/-!
# Examples.ImperfectInformation.State

Topic: equilibria   Node: 15e0096078fc

Provenance: formalization of a published result. Source: EconCSLib, `Examples.ImperfectInformation.State`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Examples.ImperfectInformation.State
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
inductive Examples.ImperfectInformation.State | root | left | right | stop
  deriving DecidableEq
