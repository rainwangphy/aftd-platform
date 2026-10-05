import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetMinSet
import AFTD.Kb.Tcs.PmMinPre

/-!
# pm_minPre_n

Topic: algorithms   Node: cf4682c76a6a

The minimal elements of the full prefix of length n are the minimal elements of the poset.
-/

theorem pm_minPre_n {n : ℕ} (P : PMPoset n) : pmMinPre P n = P.minSet := by
  ext a
  simp [pmMinPre, PMPoset.minSet]
