import AFTD.Prelude

/-!
# coprime_matching_coeff

Topic: elementary_number_theory   Node: 331e64ccf875

Provenance: helper lemma. step towards coprime_matching_of_exponent_lt_prime

The (k,j) entry of the change-of-basis matrix: at primes p dividing b only the identity term k_p = j_p survives (coefficient 1), at the other primes it is the binomial coefficient binom(j_p,k_p) times ζ_p^(a k_p) times (−1)^(j_p−k_p).
-/

/-- Change-of-basis coefficient from the (y-1)-basis to the Vandermonde (base^t)-basis. -/
noncomputable def coprime_matching_coeff (a b : Nat) (z : Nat → Complex) (S : Finset Nat) (k j : Nat →₀ Nat) : Complex := ∏ p ∈ S, if p ∣ b then (if k p = j p then 1 else 0) else ((j p).choose (k p) : Complex) * (z p) ^ (a * k p) * (-1 : Complex) ^ (j p - k p)
