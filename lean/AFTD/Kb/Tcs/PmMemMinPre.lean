import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PmMinPre

/-!
# pm_mem_minPre

Topic: algorithms   Node: 471b1d40745b

Every minimal element of the prefix of length k has index below k and no element of index below k lies below it.
-/

theorem pm_mem_minPre {n : ℕ} (P : PMPoset n) (k : ℕ) (t : Fin n) (ht : t ∈ pmMinPre P k) :
    t.val < k ∧ ∀ b : Fin n, b.val < k → P.lt b t = false := by
  simpa [pmMinPre] using ht
