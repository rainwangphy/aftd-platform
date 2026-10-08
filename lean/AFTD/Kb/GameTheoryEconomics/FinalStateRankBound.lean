import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSDAState
import AFTD.Kb.GameTheoryEconomics.GSIsFree
import AFTD.Kb.GameTheoryEconomics.GSPropTarget
import AFTD.Kb.GameTheoryEconomics.GSDaRun
import AFTD.Kb.GameTheoryEconomics.GSDaStep
import AFTD.Kb.GameTheoryEconomics.GSFinalState
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.ProposalRankBoundRun
import AFTD.Kb.GameTheoryEconomics.GSInitState

/-!
# finalState_rank_bound

Topic: matching_markets   Node: 70b80a723666

Provenance: formalization of a published result. Source: EconCSLib, `finalState_rank_bound`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At termination: if man j proposed to woman i at some round (j was free, i was his nc-th choice at state s, and the rest of the run reaches finalState), woman i's final partner has rank ≤ j in w.prefs i.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
/-- At termination: if man j proposed to woman i at some round (j was free, i was his nc-th choice at state s, and the rest of the run reaches finalState), woman i's final partner has rank ≤ j in w.prefs i. -/
lemma finalState_rank_bound (w m : Preferences n) (fuel : ℕ) (s : DAState n)
    (j i : Fin n) (hfj : isFree s j = true) (hpt : propTarget m j (s.nextChoice j) = some i)
    (hrun : daRun w m fuel (daStep w m s) = finalState w m) :
    (w.prefs i).idxOf (gs w m i) ≤ (w.prefs i).idxOf j := by
  obtain ⟨h, hh, hrk⟩ := proposal_rank_bound_run w m fuel s j i hfj hpt
  rw [hrun] at hh
  -- gs w m i = h (woman i holds man h at termination)
  have hgs : gs w m i = h := by
    simp only [gs, finalState]
    rw [show (daRun w m (n * n + 1) (initState n)).holding i = some h from hh]; simp
  rw [hgs]; exact hrk
