import AFTD.Prelude

/-!
# coprime_matching_base

Topic: elementary_number_theory   Node: b940f87cda9f

Provenance: helper lemma. step towards coprime_matching_of_exponent_lt_prime

The base attached to prime p in the Vandermonde matrix: the prime p itself when p divides b, and ζ^b (a primitive p-th root of unity, since p does not divide b) otherwise.
-/

/-- Vandermonde base at prime p: p when p ∣ b, and z_p^b otherwise. -/
noncomputable def coprime_matching_base (b : Nat) (z : Nat → Complex) (p : Nat) : Complex := if p ∣ b then (p : Complex) else (z p) ^ b
