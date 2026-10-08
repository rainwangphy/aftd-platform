import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree

/-!
# GS.isFree_iff

Topic: matching_markets   Node: a876f08060c0

Provenance: formalization of a published result. Source: EconCSLib, `GS.isFree_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.isFree_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
lemma GS.isFree_iff {n : ℕ} (s : DAState n) (i : Fin n) :
    isFree s i = true ↔ ∀ j : Fin n, s.holding j ≠ some i := by simp [isFree]
