import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PMTree
import AFTD.Kb.Tcs.PMTreeCost
import AFTD.Kb.Tcs.PmAlg

/-!
# pm_alg_cost

Topic: algorithms   Node: c6d9b932699e

Cost bound: at most two queries per element, one for the second element, none for the first.
-/

/-- Cost bound: at most two queries per element, one for the second element, none for the first. -/
theorem pm_alg_cost {n : ℕ} (P : PMPoset n) : ∀ (m k : ℕ) (cs : List (Fin n)),
    cs.length ≤ 2 →
    ((pmAlg m k cs).cost P : ℤ) ≤ max 0 (2 * (m : ℤ) -
      (if cs.length = 0 then 3 else if cs.length = 1 then 1 else 0)) := by
  intro m
  induction m with
  | zero =>
    intro k cs _
    simp [pmAlg, PMTree.cost]
  | succ m ih =>
    intro k cs hlen
    by_cases hk : k < n
    · rcases cs with _ | ⟨t, _ | ⟨t2, _ | ⟨t3, rest⟩⟩⟩
      · have := ih (k + 1) [⟨k, hk⟩] (by simp)
        simp only [pmAlg, dif_pos hk]
        simp at this ⊢
        omega
      · have h1 := ih (k + 1) [⟨k, hk⟩] (by simp)
        have h2 := ih (k + 1) [t] (by simp)
        have h3 := ih (k + 1) [t, ⟨k, hk⟩] (by simp)
        simp only [pmAlg, dif_pos hk, PMTree.cost]
        simp at h1 h2 h3 ⊢
        cases P.ans ⟨k, hk⟩ t <;> simp <;> push_cast <;> omega
      · have h1 := ih (k + 1) [⟨k, hk⟩] (by simp)
        have h2 := ih (k + 1) [t, t2] (by simp)
        have h3 := ih (k + 1) [t2, ⟨k, hk⟩] (by simp)
        have h4 := ih (k + 1) [t, ⟨k, hk⟩] (by simp)
        simp only [pmAlg, dif_pos hk, PMTree.cost]
        simp at h1 h2 h3 h4 ⊢
        cases P.ans ⟨k, hk⟩ t <;> (try simp [PMTree.cost]) <;>
          cases P.ans ⟨k, hk⟩ t2 <;> (try simp) <;> push_cast <;> omega
      · simp at hlen
    · simp only [pmAlg, dif_neg hk, PMTree.cost]
      simp
