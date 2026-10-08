import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState

/-!
# GS.isFree

Topic: matching_markets   Node: 847755b6a0e3

Provenance: formalization of a published result. Source: EconCSLib, `GS.isFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Man `i` is free in `s` iff no woman holds him.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- Man `i` is free in `s` iff no woman holds him. -/
def GS.isFree {n : ℕ} (s : DAState n) (i : Fin n) : Bool :=
  decide (∀ j : Fin n, s.holding j ≠ some i)
