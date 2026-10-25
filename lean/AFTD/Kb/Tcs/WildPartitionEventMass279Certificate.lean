import AFTD.Prelude

/-!
# wild_partition_event_mass_279_certificate

Topic: graphs   Node: d8f58e5e8d86

Provenance: helper lemma. Arithmetic helper for the proposed OP-306 permutation-local-lemma proof; arXiv:2610.22142, Section 3.3.2 (seals), and experiments 4503 and 4505. The term h=0 is zero; h=1..46 represents the smaller side of every possible seal cut in 93 triple blocks.

The exact rational sum of weighted per-position seal-event masses at n=279 and a=323/279 is at most 701/10000, and a*(1-701/10000)^2 is at least one. This is an arithmetic certificate, not a bound on the wild number.
-/

theorem wild_partition_event_mass_279_certificate :
    (∑ h ∈ Finset.range 47,
      (3 * h : ℚ) * (Nat.choose 93 h : ℚ) *
        (Nat.choose 139 (3 * h / 2) : ℚ) / (Nat.choose 279 (3 * h) : ℚ) *
        (323 / 279 : ℚ) ^ (3 * h)) ≤ 701 / 10000 ∧
    (323 / 279 : ℚ) * (1 - 701 / 10000) ^ 2 ≥ 1 := by
  constructor
  · simp only [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
  · norm_num
