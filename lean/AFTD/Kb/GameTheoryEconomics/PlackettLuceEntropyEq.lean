import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceEntropy
import AFTD.Kb.GameTheoryEconomics.SumRankingsOfNonempty
import AFTD.Kb.GameTheoryEconomics.PlackettLuceProbCons
import AFTD.Kb.GameTheoryEconomics.SumPlackettLuceProb

/-!
# plackett_luce_entropy_eq

Topic: social_choice   Node: b863af70d83c

Chain rule: the Plackett-Luce entropy on S equals the entropy of the first choice plus the expected Plackett-Luce entropy of the remaining alternatives.
-/

/-- Chain rule (grouping by the top-ranked alternative). -/
lemma plackett_luce_entropy_eq (w : ℕ → ℝ) (S : Finset ℕ) (hS : S.Nonempty)
    (hw : ∀ b ∈ S, 0 < w b) :
    plackett_luce_entropy w S =
      ∑ a ∈ S, Real.negMulLog (w a / ∑ b ∈ S, w b) +
        ∑ a ∈ S, w a / (∑ b ∈ S, w b) * plackett_luce_entropy w (S.erase a) := by
  unfold plackett_luce_entropy
  rw [sum_rankings_of_nonempty S hS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h1 := sum_plackett_luce_prob w _ (S.erase a) rfl (fun b hb => hw b (Finset.mem_of_mem_erase hb))
  rw [Finset.sum_congr rfl fun t ht => by rw [plackett_luce_prob_cons w S a ha t ht, Real.negMulLog_mul],
    Finset.sum_add_distrib, ← Finset.sum_mul, h1, one_mul, ← Finset.mul_sum]
