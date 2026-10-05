import AFTD.Prelude
import AFTD.Kb.Tcs.PMTreeCorrect2
import AFTD.Kb.Tcs.PmMinPre
import AFTD.Kb.Tcs.PmMinPreN
import AFTD.Kb.Tcs.PmAlg
import AFTD.Kb.Tcs.PmAlgRun

/-!
# pm_alg_correct

Topic: algorithms   Node: 44a0874aa024

The algorithm is correct on every width-2 poset.
-/

/-- The algorithm is correct on every width-2 poset. -/
theorem pm_alg_correct (n : ℕ) : (pmAlg (n := n) n 0 []).Correct2 := by
  intro P hP
  rw [← pm_minPre_n]
  exact pm_alg_run P hP n 0 [] (by omega) (by simp) (by simp)
    (by ext a; simp [pmMinPre])
