import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree

/-!
# GS.freeMenSet

Topic: matching_markets   Node: 1d17423a1741

Provenance: formalization of a published result. Source: EconCSLib, `GS.freeMenSet`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The finset of all free men in `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
/-- The finset of all free men in `s`. -/
def GS.freeMenSet {n : ℕ} (s : DAState n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => isFree s i)
