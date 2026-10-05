import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseInDomain
import AFTD.Kb.GameTheoryEconomics.FseSurjective
import AFTD.Kb.GameTheoryEconomics.FseSPAll
import AFTD.Kb.GameTheoryEconomics.FseLemmaC
import AFTD.Kb.GameTheoryEconomics.FseMemRange

/-!
# fse_follow

Topic: mechanism_design   Node: f4e680a6ebf4

Moving the coordinate of agent i when i's location is not shared and the outcome is at i's location: the outcome follows agent i.
-/

/-- Moving the coordinate of agent `i` when `i`'s location is not shared and the outcome is at `i`'s location: the outcome follows agent `i`. -/
lemma fse_follow {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hSP : fse_SPAll f) (hsurj : fse_Surjective f)
    (c : Fin n → ℝ) (hc : fse_InDomain c) (i : Fin n) (hfc : f c = c i)
    (huniq : ∀ k, k ≠ i → c k ≠ c i) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (Function.update c i t) = t := by
  have hc' : fse_InDomain (Function.update c i t) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [ht]
    · simp [Function.update_of_ne hk, hc k]
  by_contra hne
  obtain ⟨k, hk⟩ := fse_mem_range f hSP hsurj _ hc'
  have hki : k ≠ i := by
    intro h; subst h; simp at hk; exact hne hk
  rcases fse_lemmaC f hSP _ hc' i (c i) (hc i) with h | h
  · simp at h; exact hne h
  · rw [Function.update_idem, Function.update_eq_self] at h
    rw [Function.update_of_ne hki] at hk
    exact huniq k hki (by rw [← hk, ← h, hfc])
