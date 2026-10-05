import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PmMinPre
import AFTD.Kb.Tcs.PmMinPreSucc

/-!
# pm_step_eq

Topic: algorithms   Node: db52b9623b4b

One scanning step of the candidate algorithm maintains the invariant that its candidate list is exactly the set of minimal elements of the current prefix.
-/

open Finset in
theorem pm_step_eq {n : ℕ} (P : PMPoset n) (k : ℕ) (hk : k < n) (old new : List (Fin n))
    (hold : old.toFinset = pmMinPre P k)
    (h : ∀ a, a ∈ new ↔ (a ∈ old ∧ P.lt ⟨k, hk⟩ a = false) ∨
      (a = ⟨k, hk⟩ ∧ ∀ t ∈ old, P.lt t ⟨k, hk⟩ = false)) :
    new.toFinset = pmMinPre P (k + 1) := by
  ext a
  rw [List.mem_toFinset, h a, pm_minPre_succ P k hk, ← hold]
  simp only [List.mem_toFinset]
