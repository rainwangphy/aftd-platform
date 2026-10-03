import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingsOf
import AFTD.Kb.GameTheoryEconomics.MemRankingsOfIff

/-!
# rankings_of_empty

Topic: social_choice   Node: 16c77eb8ea80

The empty set has exactly one ranking, the empty list.
-/

lemma rankings_of_empty : rankings_of ∅ = {[]} := by
  ext l
  rw [mem_rankings_of_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩; simpa using h
  · rintro rfl; simp
