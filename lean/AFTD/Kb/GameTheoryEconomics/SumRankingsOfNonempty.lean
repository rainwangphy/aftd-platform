import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingsOf
import AFTD.Kb.GameTheoryEconomics.RankingsOfEqBiUnion

/-!
# sum_rankings_of_nonempty

Topic: social_choice   Node: 84e501aa2b59

For nonempty S, a sum over rankings of S splits as a sum over the top alternative a and the rankings of S minus a.
-/

lemma sum_rankings_of_nonempty (S : Finset ℕ) (hS : S.Nonempty) (f : List ℕ → ℝ) :
    ∑ l ∈ rankings_of S, f l = ∑ a ∈ S, ∑ t ∈ rankings_of (S.erase a), f (a :: t) := by
  rw [rankings_of_eq_biUnion S hS, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_image]
    intro x _ y _ h; exact List.cons_injective h
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨t1, -, rfl⟩ := h1
    obtain ⟨t2, -, h⟩ := h2
    exact hab (List.cons.inj h).1.symm
