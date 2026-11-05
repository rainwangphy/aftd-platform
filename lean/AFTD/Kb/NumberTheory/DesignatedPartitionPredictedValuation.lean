import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedPartitionA3

/-!
# designated_partition_predicted_valuation

Topic: elementary_number_theory   Node: 6ff19e06fadc

Provenance: formalization of a published result. Source: arXiv:2611.05623 Conjecture 6.1

The function mapping each natural number k to 3 if k % 16 = 2, and to padicValNat 2 (designated_partition_a3 k) otherwise.
-/

/-- The predicted 2-adic valuation of A_k(4n+3): 3 if k ≡ 2 mod 16, else v_2(A_k(3)). -/
def designated_partition_predicted_valuation (k : ℕ) : ℕ := if k % 16 = 2 then 3 else padicValNat 2 (designated_partition_a3 k)
