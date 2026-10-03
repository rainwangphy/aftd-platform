import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingsOf

/-!
# mem_rankings_of_iff

Topic: social_choice   Node: 5236797f27ef

A list is a ranking of S iff it has no duplicates and its set of entries is S.
-/

lemma mem_rankings_of_iff (S : Finset ℕ) (l : List ℕ) :
    l ∈ rankings_of S ↔ l.Nodup ∧ l.toFinset = S := by
  unfold rankings_of
  rw [List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.nodup_iff.2 S.nodup_toList, by rw [List.toFinset_eq_of_perm _ _ h, Finset.toList_toFinset]⟩
  · rintro ⟨hn, hs⟩
    exact List.perm_of_nodup_nodup_toFinset_eq hn S.nodup_toList (by rw [hs, Finset.toList_toFinset])
