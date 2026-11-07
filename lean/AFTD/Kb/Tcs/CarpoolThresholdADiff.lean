import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolThresholdA

/-!
# carpool_threshold_A_diff

Topic: online_algorithms   Node: 26c3af3be1ce

Provenance: formalization of a published result. Source: arXiv:2611.00388 Section 4.1

For any integer threshold D : ℤ and natural number k : ℕ, the forward difference carpool_threshold_A D (k + 1) - carpool_threshold_A D k equals D - 30 * (k : ℤ).
-/

/-- Forward increment of the threshold function: A(k+1) - A(k) = D - 30*k. -/
theorem carpool_threshold_A_diff (D : ℤ) (k : ℕ) :
    carpool_threshold_A D (k + 1) - carpool_threshold_A D k = D - 30 * (k : ℤ) := by
  unfold carpool_threshold_A
  push_cast
  ring
