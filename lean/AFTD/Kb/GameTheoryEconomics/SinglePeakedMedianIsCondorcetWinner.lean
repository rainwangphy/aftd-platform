import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetWinner
import AFTD.Kb.GameTheoryEconomics.IsSinglePeaked
import AFTD.Kb.GameTheoryEconomics.SinglePeakedMedianDefeatsLess
import AFTD.Kb.GameTheoryEconomics.SinglePeakedMedianDefeatsGreater
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# single_peaked_median_is_condorcet_winner

Topic: social_choice   Node: 010622fad7f7

Provenance: formalization of a published result. Source: Duncan Black, 'On the Rationale of Group Decision-making', Journal of Political Economy 56(1):23-34 (1948)

Under single-peaked preferences with asymmetric preferences, if an alternative m satisfies that strictly more than half of the voters have peak at least m and strictly more than half have peak at most m, then m is a Condorcet winner.
-/

/-- Black's Median Voter Theorem: an alternative m satisfying the median peak inequalities is a Condorcet winner. -/
theorem single_peaked_median_is_condorcet_winner {V A : Type*} [Fintype V] [LinearOrder A]
    (P : V → A → A → Prop) [∀ v, DecidableRel (P v)]
    (hasymm : ∀ v x y, P v x y → ¬ P v y x)
    (peak : V → A) (hsp : ∀ v, is_single_peaked (P v) (peak v))
    (m : A)
    (h_ge : Fintype.card V < 2 * (Finset.filter (fun v => m ≤ peak v) Finset.univ).card)
    (h_le : Fintype.card V < 2 * (Finset.filter (fun v => peak v ≤ m) Finset.univ).card) :
    condorcet_winner P m := by
  intro y hy
  rcases lt_or_gt_of_ne hy with hym | hym
  · exact single_peaked_median_defeats_less P hasymm peak hsp m h_ge y hym
  · exact single_peaked_median_defeats_greater P hasymm peak hsp m h_le y hym
