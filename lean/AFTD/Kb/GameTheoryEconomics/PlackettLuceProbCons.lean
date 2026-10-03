import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceProb
import AFTD.Kb.GameTheoryEconomics.RankingsOf
import AFTD.Kb.GameTheoryEconomics.MapSumOfMemRankingsOf

/-!
# plackett_luce_prob_cons

Topic: social_choice   Node: a478bb6017b8

If a is in S and t ranks S minus a, the Plackett-Luce probability of a followed by t is w(a)/w(S) times that of t.
-/

lemma plackett_luce_prob_cons (w : ℕ → ℝ) (S : Finset ℕ) (a : ℕ) (ha : a ∈ S) (t : List ℕ)
    (ht : t ∈ rankings_of (S.erase a)) :
    plackett_luce_prob w (a :: t) = w a / (∑ b ∈ S, w b) * plackett_luce_prob w t := by
  rw [plackett_luce_prob, map_sum_of_mem_rankings_of w _ t ht, Finset.add_sum_erase S w ha]
