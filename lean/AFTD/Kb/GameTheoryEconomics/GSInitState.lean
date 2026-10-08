import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState

/-!
# GS.initState

Topic: matching_markets   Node: a3029f78b360

Provenance: formalization of a published result. Source: EconCSLib, `GS.initState`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Initial state: all women free, all men start at proposal index 0.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- Initial state: all women free, all men start at proposal index 0. -/
def GS.initState (n : ℕ) : DAState n :=
  { nextChoice := fun _ => 0, holding := fun _ => none }
