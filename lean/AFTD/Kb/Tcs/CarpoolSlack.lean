import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolThresholdA

/-!
# carpool_slack

Topic: online_algorithms   Node: ec7934234268

Provenance: formalization of a published result. Source: arXiv:2611.00388 Section 4.1

The discrepancy slack carpool_slack taking an integer threshold D : ℤ, a discrepancy vector d : Fin n → ℤ, and a finite vertex subset S : Finset (Fin n) as arguments, defined as the integer (∑ i ∈ S, d i) - carpool_threshold_A D S.card.
-/

/-- Discrepancy slack Lambda(d, S) = d(S) - A(|S|) of a vertex subset S. -/
def carpool_slack {n : ℕ} (D : ℤ) (d : Fin n → ℤ) (S : Finset (Fin n)) : ℤ := (∑ i ∈ S, d i) - carpool_threshold_A D S.card
