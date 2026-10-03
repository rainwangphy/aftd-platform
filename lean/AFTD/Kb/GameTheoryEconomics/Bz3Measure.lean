import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PropensityBanzhafMeasure
import AFTD.Kb.GameTheoryEconomics.Bz3Cnt
import AFTD.Kb.GameTheoryEconomics.Bz3Coal
import AFTD.Kb.GameTheoryEconomics.Bz3Pattern
import AFTD.Kb.GameTheoryEconomics.Bz3IteEq
import AFTD.Kb.GameTheoryEconomics.Bz3SumFour

/-!
# bz3_measure

Topic: general_equilibrium   Node: 50995f708e5e

For three players and p = q = 1/2, the Banzhaf measure of a player is a quarter of its pivot count.
-/

lemma bz3_measure (w : Fin 3 → ℝ) (i : Fin 3) :
    propensity_banzhaf_measure (1 / 2) (1 / 2) w i = (bz3_cnt (bz3_pattern w) i : ℝ) / 4 := by
  unfold propensity_banzhaf_measure
  simp only [bz3_ite_eq]
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · rw [show (Finset.univ.erase (0 : Fin 3)).powerset = {∅, {1}, {2}, {1, 2}} from by decide,
      bz3_sum_four _ _ _ (by decide)]
    simp only [show insert (0 : Fin 3) (∅ : Finset (Fin 3)) = {0} from by decide,
      show insert (0 : Fin 3) ({1} : Finset (Fin 3)) = {0, 1} from by decide,
      show insert (0 : Fin 3) ({2} : Finset (Fin 3)) = {0, 2} from by decide,
      show insert (0 : Fin 3) ({1, 2} : Finset (Fin 3)) = {0, 1, 2} from by decide]
    simp only [bz3_cnt, bz3_pattern, bz3_coal, Matrix.cons_val, Finset.card_empty, Finset.card_singleton,
      Finset.card_pair (show (1 : Fin 3) ≠ 2 by decide)]
    norm_num
    ring
  · rw [show (Finset.univ.erase (1 : Fin 3)).powerset = {∅, {0}, {2}, {0, 2}} from by decide,
      bz3_sum_four _ _ _ (by decide)]
    simp only [show insert (1 : Fin 3) (∅ : Finset (Fin 3)) = {1} from by decide,
      show insert (1 : Fin 3) ({0} : Finset (Fin 3)) = {0, 1} from by decide,
      show insert (1 : Fin 3) ({2} : Finset (Fin 3)) = {1, 2} from by decide,
      show insert (1 : Fin 3) ({0, 2} : Finset (Fin 3)) = {0, 1, 2} from by decide]
    simp only [bz3_cnt, bz3_pattern, bz3_coal, Matrix.cons_val, Finset.card_empty, Finset.card_singleton,
      Finset.card_pair (show (0 : Fin 3) ≠ 2 by decide)]
    norm_num
    ring
  · rw [show (Finset.univ.erase (2 : Fin 3)).powerset = {∅, {0}, {1}, {0, 1}} from by decide,
      bz3_sum_four _ _ _ (by decide)]
    simp only [show insert (2 : Fin 3) (∅ : Finset (Fin 3)) = {2} from by decide,
      show insert (2 : Fin 3) ({0} : Finset (Fin 3)) = {0, 2} from by decide,
      show insert (2 : Fin 3) ({1} : Finset (Fin 3)) = {1, 2} from by decide,
      show insert (2 : Fin 3) ({0, 1} : Finset (Fin 3)) = {0, 1, 2} from by decide]
    simp only [bz3_cnt, bz3_pattern, bz3_coal, Matrix.cons_val, Finset.card_empty, Finset.card_singleton,
      Finset.card_pair (show (0 : Fin 3) ≠ 1 by decide)]
    norm_num
    ring
