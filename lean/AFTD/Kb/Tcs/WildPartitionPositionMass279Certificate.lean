import AFTD.Prelude

/-!
# wild_partition_position_mass_279_certificate

Topic: graphs   Node: 23127cafdd0f

Provenance: helper lemma. arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Section 6, Conjecture

For n=279 and a=323/279: the sum over block counts h=1..46 of 279*C(92,h-1)*(3h)!*C(139,floor(3h/2))*a^(3h)/(279)_(3h) is at most 701/10000 (the local-lemma event mass through one position). Arithmetic certificate.
-/

theorem wild_partition_position_mass_279_certificate :
    ∑ m ∈ Finset.range 93, ((Nat.choose 92 m : ℕ) : ℚ) *
      (if m + 1 ≤ 46 then (279 : ℚ) * (((3 * (m + 1)).factorial * Nat.choose 139 (3 * (m + 1) / 2) : ℕ) : ℚ) *
        ((323 / 279 : ℚ) ^ (3 * (m + 1)) / ((Nat.descFactorial 279 (3 * (m + 1)) : ℕ) : ℚ)) else 0)
        ≤ 701 / 10000 := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel
