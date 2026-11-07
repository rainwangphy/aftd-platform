import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolThresholdA
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# carpool_delta_sum

Topic: online_algorithms   Node: 97809f9428d4

Provenance: helper lemma. arXiv:2611.00388 Eq. (4.4)

For any integer threshold D : ℤ, integer discrepancies da db : ℤ satisfying da - db ≤ 29, and natural number k ≥ 1, the sum of delta_plus = db - (carpool_threshold_A D (k + 1) - carpool_threshold_A D k) and delta_minus = -da + (carpool_threshold_A D k - carpool_threshold_A D (k - 1)) is at least 1.
-/

/-- The sum of gains Delta_+ and Delta_- along a crossing edge is at least 1 when the receiving gap is at most 29. -/
theorem carpool_delta_sum (D : ℤ) (da db : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hgap : da - db ≤ 29) :
    let delta_plus := db - (carpool_threshold_A D (k + 1) - carpool_threshold_A D k)
    let delta_minus := -da + (carpool_threshold_A D k - carpool_threshold_A D (k - 1))
    delta_plus + delta_minus ≥ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  dsimp [carpool_threshold_A]
  ring_nf
  linarith
