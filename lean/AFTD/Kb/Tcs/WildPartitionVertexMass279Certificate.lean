import AFTD.Prelude

/-!
# wild_partition_vertex_mass_279_certificate

Topic: graphs   Node: 1ca3b49f7620

Provenance: helper lemma. arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Section 6, Conjecture

For n=279 and a=323/279: the sum over block counts h=1..46 of C(93,h)*(3h)!*([3h odd]C(139,floor(3h/2))+278*C(138,floor(3h/2)-1))*a^(3h)/(279)_(3h) is at most 701/10000 (the local-lemma event mass through one vertex). Arithmetic certificate.
-/

theorem wild_partition_vertex_mass_279_certificate :
    ∑ m ∈ Finset.range 94, ((Nat.choose 93 m : ℕ) : ℚ) *
      (if 1 ≤ m ∧ m ≤ 46 then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose 139 (3 * m / 2) else 0)
        + 278 * ((3 * m).factorial * Nat.choose 138 (3 * m / 2 - 1)) : ℕ) : ℚ)) *
        ((323 / 279 : ℚ) ^ (3 * m) / ((Nat.descFactorial 279 (3 * m) : ℕ) : ℚ)) else 0) ≤ 701 / 10000 := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel
