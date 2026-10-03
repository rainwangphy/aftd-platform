import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingsOf
import AFTD.Kb.GameTheoryEconomics.MemRankingsOfIff

/-!
# map_sum_of_mem_rankings_of

Topic: social_choice   Node: e6ecd5e08a33

The total weight of the entries of a ranking of S is the total weight of S.
-/

lemma map_sum_of_mem_rankings_of (w : ℕ → ℝ) (S : Finset ℕ) (t : List ℕ)
    (ht : t ∈ rankings_of S) : (t.map w).sum = ∑ b ∈ S, w b := by
  rw [mem_rankings_of_iff] at ht
  rw [← ht.2, List.sum_toFinset _ ht.1]
