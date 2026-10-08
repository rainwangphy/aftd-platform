import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSFreeMenSet
import AFTD.Kb.GameTheoryEconomics.GSIsFree

/-!
# GS.mem_freeMenSet

Topic: matching_markets   Node: 880fc5e19d5a

Provenance: formalization of a published result. Source: EconCSLib, `GS.mem_freeMenSet`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GS.mem_freeMenSet
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
lemma GS.mem_freeMenSet {n : ℕ} {s : DAState n} {i : Fin n} :
    i ∈ freeMenSet s ↔ isFree s i = true := by simp [freeMenSet]
