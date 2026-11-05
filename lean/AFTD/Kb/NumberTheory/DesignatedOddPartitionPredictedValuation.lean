import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedOddPartitionB3

/-!
# designated_odd_partition_predicted_valuation

Topic: elementary_number_theory   Node: 10113001d1a6

Provenance: formalization of a published result. Source: arXiv:2611.05623, Conjecture 6.2

The function designated_odd_partition_predicted_valuation mapping each natural number k to 2 if k % 8 = 1, to 3 if k % 8 = 6, and to padicValNat 2 (designated_odd_partition_b3 k) otherwise.
-/

/-- Predicted minimum 2-adic valuation of B_k(4n+3). -/
def designated_odd_partition_predicted_valuation (k : ℕ) : ℕ := if k % 8 = 1 then 2 else if k % 8 = 6 then 3 else padicValNat 2 (designated_odd_partition_b3 k)
