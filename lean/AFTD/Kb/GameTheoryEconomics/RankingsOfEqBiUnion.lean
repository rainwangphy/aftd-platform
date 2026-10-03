import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingsOf
import AFTD.Kb.GameTheoryEconomics.MemRankingsOfIff

/-!
# rankings_of_eq_biUnion

Topic: social_choice   Node: 76f3fd35539b

For nonempty S, the rankings of S are obtained by choosing a top alternative a in S and then a ranking of S minus a.
-/

lemma rankings_of_eq_biUnion (S : Finset ℕ) (hS : S.Nonempty) :
    rankings_of S = S.biUnion (fun a => (rankings_of (S.erase a)).image (List.cons a)) := by
  ext l
  simp only [Finset.mem_biUnion, Finset.mem_image, mem_rankings_of_iff]
  constructor
  · rintro ⟨hn, hs⟩
    cases l with
    | nil => simp at hs; exact absurd hs.symm hS.ne_empty
    | cons a t =>
      rw [List.nodup_cons] at hn
      have ha : a ∈ S := by rw [← hs]; simp
      refine ⟨a, ha, t, ⟨hn.2, ?_⟩, rfl⟩
      rw [← hs, List.toFinset_cons, Finset.erase_insert (by simpa using hn.1)]
  · rintro ⟨a, ha, t, ⟨hn, hs⟩, rfl⟩
    have hat : a ∉ t := by
      intro h
      have : a ∈ t.toFinset := List.mem_toFinset.2 h
      rw [hs] at this; simp at this
    refine ⟨List.nodup_cons.2 ⟨hat, hn⟩, ?_⟩
    rw [List.toFinset_cons, hs, Finset.insert_erase ha]
