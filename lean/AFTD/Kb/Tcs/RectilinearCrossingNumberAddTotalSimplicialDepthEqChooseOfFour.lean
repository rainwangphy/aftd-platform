import AFTD.Prelude
import AFTD.Kb.Tcs.RectilinearCrossingNumberEqSumPowersetCardFour
import AFTD.Kb.Tcs.TotalSimplicialDepthEqSumPowersetCardFour
import AFTD.Kb.Tcs.TotalSimplicialDepth
import AFTD.Kb.Tcs.RectilinearCrossingNumber

/-!
# rectilinear_crossing_number_add_total_simplicial_depth_eq_choose_of_four

Topic: combinatorics   Node: 260a42897df4

Provenance: helper lemma. arXiv:2610.38658 Lemma 20 -- Larger Crossing Families

If every 4-element subset Q of a finite point set P in the Euclidean plane satisfies cr(Q) + TSD(Q) = 1, then cr(P) + TSD(P) = (|P| choose 4).
-/

/-- Double-counting reduction: if every 4-element subset contributes 1 to cr + TSD, the total sum is (|P| choose 4). -/
theorem rectilinear_crossing_number_add_total_simplicial_depth_eq_choose_of_four
    (P : Finset (ℝ × ℝ))
    (h_four : ∀ Q ∈ P.powersetCard 4, rectilinear_crossing_number Q + total_simplicial_depth Q = 1) :
    rectilinear_crossing_number P + total_simplicial_depth P = Nat.choose P.card 4 := by
  rw [rectilinear_crossing_number_eq_sum_powersetCard_four,
      total_simplicial_depth_eq_sum_powersetCard_four,
      ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl h_four]
  simp [Finset.card_powersetCard]
