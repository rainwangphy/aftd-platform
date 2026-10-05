import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetWidth2
import AFTD.Kb.Tcs.PMTree
import AFTD.Kb.Tcs.PMTreeCost
import AFTD.Kb.Tcs.PMTreeCorrect2
import AFTD.Kb.Tcs.PmMain
import AFTD.Kb.Tcs.PmInit
import AFTD.Kb.Tcs.PmInitInv
import AFTD.Kb.Tcs.PmInitPot

/-!
# pm_lower_bound

Topic: algorithms   Node: 2f85b453e790

Deterministic lower bound for 1-selection at width 2. Every deterministic comparison algorithm that finds the set of minimal elements of every poset of width at most 2 on n elements makes at least 2n − 3 queries on some such poset. (arXiv 0707.1532 proves (w+1)n/2 − w = 3n/2 − 2 for w = 2.)
-/

/-- **Deterministic lower bound for 1-selection at width 2.** Every deterministic comparison algorithm that finds the set of minimal elements of every poset of width at most `2` on `n` elements makes at least `2n − 3` queries on some such poset. (arXiv 0707.1532 proves `(w+1)n/2 − w = 3n/2 − 2` for `w = 2`.) -/
theorem pm_lower_bound {n : ℕ} (T : PMTree n) (hT : T.Correct2) :
    ∃ P : PMPoset n, P.Width2 ∧ 2 * (n : ℤ) - 3 ≤ T.cost P := by
  obtain ⟨P, hP, _, h⟩ := pm_main T (pmInit n) (pm_init_inv n)
    (fun P hP _ => hT P hP)
  exact ⟨P, hP, by rw [← pm_init_pot]; exact h⟩
