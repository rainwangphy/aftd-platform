import AFTD.Prelude

/-!
# restricted_base_ell_partition

Topic: elementary_number_theory   Node: 7d56978b8656

Provenance: formalization of a published result. Source: arXiv:2611.08109 Section 1

For integers k, ℓ, and n, the restricted base-ℓ partition function b_{k,ℓ}(n) is the number of partitions of n into powers of ℓ where each part appears at most k times.
-/

open scoped Classical in
/-- The number of partitions of n into powers of ℓ with each part appearing at most k times. -/
noncomputable def restricted_base_ell_partition (k ℓ n : ℕ) : ℕ := ((Nat.Partition.restricted n (fun i => ∃ j : ℕ, i = ℓ ^ j)) ∩
    (Nat.Partition.countRestricted n (k + 1))).card
