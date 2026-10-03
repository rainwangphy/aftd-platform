import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceProb
import AFTD.Kb.GameTheoryEconomics.RankingsOf
import AFTD.Kb.GameTheoryEconomics.RankingsOfEmpty
import AFTD.Kb.GameTheoryEconomics.SumRankingsOfNonempty
import AFTD.Kb.GameTheoryEconomics.PlackettLuceProbCons

/-!
# sum_plackett_luce_prob

Topic: social_choice   Node: 97d014f1e4fd

With positive weights, the Plackett-Luce probabilities of the rankings of S sum to 1.
-/

lemma sum_plackett_luce_prob (w : ℕ → ℝ) :
    ∀ n (S : Finset ℕ), S.card = n → (∀ b ∈ S, 0 < w b) →
      ∑ l ∈ rankings_of S, plackett_luce_prob w l = 1 := by
  intro n
  induction n with
  | zero =>
    intro S hS _
    rw [Finset.card_eq_zero.1 hS, rankings_of_empty, Finset.sum_singleton, plackett_luce_prob]
  | succ n ih =>
    intro S hS hw
    have hne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hW : 0 < ∑ b ∈ S, w b := Finset.sum_pos hw hne
    rw [sum_rankings_of_nonempty S hne]
    calc ∑ a ∈ S, ∑ t ∈ rankings_of (S.erase a), plackett_luce_prob w (a :: t)
        = ∑ a ∈ S, w a / (∑ b ∈ S, w b) := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [Finset.sum_congr rfl fun t ht => plackett_luce_prob_cons w S a ha t ht,
            ← Finset.mul_sum,
            ih (S.erase a) (by rw [Finset.card_erase_of_mem ha]; omega)
              (fun b hb => hw b (Finset.mem_of_mem_erase hb)), mul_one]
      _ = 1 := by rw [← Finset.sum_div, div_self hW.ne']
