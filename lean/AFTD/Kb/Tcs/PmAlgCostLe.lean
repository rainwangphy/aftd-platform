import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMTreeCost
import AFTD.Kb.Tcs.PmAlg
import AFTD.Kb.Tcs.PmAlgCost

/-!
# pm_alg_cost_le

Topic: algorithms   Node: b5c763115cf0

The algorithm makes at most 2n − 3 queries (for n ≥ 2).
-/

/-- The algorithm makes at most `2n − 3` queries (for `n ≥ 2`). -/
theorem pm_alg_cost_le (n : ℕ) (hn : 2 ≤ n) (P : PMPoset n) :
    ((pmAlg (n := n) n 0 []).cost P : ℤ) ≤ 2 * (n : ℤ) - 3 := by
  have := pm_alg_cost P n 0 [] (by simp)
  simp at this
  have h2 : (2 : ℤ) ≤ n := by exact_mod_cast hn
  rcases this with h | h
  · rw [h]; push_cast; omega
  · exact h
