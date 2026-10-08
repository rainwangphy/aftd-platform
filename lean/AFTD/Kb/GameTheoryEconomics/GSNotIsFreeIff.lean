import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree

/-!
# GS.not_isFree_iff

Topic: matching_markets   Node: feb0ec34c92d

Provenance: formalization of a published result. Source: EconCSLib, `GS.not_isFree_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.not_isFree_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
lemma GS.not_isFree_iff {n : ℕ} (s : DAState n) (i : Fin n) :
    isFree s i = false ↔ ∃ j : Fin n, s.holding j = some i := by
  simp [isFree, decide_eq_false_iff_not, not_forall, ne_eq]
