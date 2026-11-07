import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolSlack
import AFTD.Kb.Tcs.CarpoolThresholdA

/-!
# carpool_slack_empty

Topic: online_algorithms   Node: 6f6155d0c681

Provenance: helper lemma. arXiv:2611.00388 Lemma 4.1

For any natural number n : ℕ, integer threshold D : ℤ, and discrepancy vector d : Fin n → ℤ, the slack carpool_slack D d (∅ : Finset (Fin n)) is zero.
-/

/-- The slack on the empty set of vertices is zero. -/
theorem carpool_slack_empty {n : ℕ} (D : ℤ) (d : Fin n → ℤ) :
    carpool_slack D d (∅ : Finset (Fin n)) = 0 := by
  simp [carpool_slack, carpool_threshold_A]
