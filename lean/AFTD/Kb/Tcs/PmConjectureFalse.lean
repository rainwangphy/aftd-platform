import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetWidth2
import AFTD.Kb.Tcs.PMTree
import AFTD.Kb.Tcs.PMTreeCost
import AFTD.Kb.Tcs.PMTreeCorrect2
import AFTD.Kb.Tcs.PmLowerBound

/-!
# pm_conjecture_false

Topic: algorithms   Node: 75030ab5dd4a

The conjecture of arXiv 0707.1532 (Section 4) that the deterministic lower bound (w+1)n/2 − w for finding the minimal elements is tight fails already for w = 2: there is no constant C such that for every n some correct deterministic algorithm uses at most (w+1)n/2 − w + C = 3n/2 − 2 + C queries on every width-2 poset.
-/

/-- **The conjecture of arXiv 0707.1532 (Section 4) that the deterministic lower bound `(w+1)n/2 − w` for finding the minimal elements is tight fails already for `w = 2`:** there is no constant `C` such that for every `n` some correct deterministic algorithm uses at most `(w+1)n/2 − w + C = 3n/2 − 2 + C` queries on every width-2 poset. -/
theorem pm_conjecture_false :
    ¬ ∃ C : ℕ, ∀ n : ℕ, ∃ T : PMTree n, T.Correct2 ∧
      ∀ P : PMPoset n, P.Width2 → 2 * (T.cost P : ℤ) ≤ 3 * (n : ℤ) - 4 + 2 * C := by
  rintro ⟨C, hC⟩
  obtain ⟨T, hT, hle⟩ := hC (2 * C + 3)
  obtain ⟨P, hP, hlow⟩ := pm_lower_bound T hT
  have := hle P hP
  push_cast at hlow this
  linarith
