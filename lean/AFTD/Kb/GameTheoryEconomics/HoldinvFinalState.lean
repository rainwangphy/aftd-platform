import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.HoldInv
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.HoldinvRun
import AFTD.Kb.GameTheoryEconomics.GSInitState
import AFTD.Kb.GameTheoryEconomics.HoldinvInit

/-!
# holdinv_finalState

Topic: matching_markets   Node: 8f8a4f2dd8b3

Provenance: formalization of a published result. Source: EconCSLib, `holdinv_finalState`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

holdinv_finalState
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
lemma holdinv_finalState (w m : Preferences n) :
    HoldInv m (finalState w m) :=
  holdinv_run w m (n * n + 1) (initState n) (holdinv_init m)
