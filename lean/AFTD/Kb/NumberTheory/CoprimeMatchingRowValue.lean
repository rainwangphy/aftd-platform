import AFTD.Prelude

/-!
# coprime_matching_row_value

Topic: elementary_number_theory   Node: 2bb980268e51

Provenance: helper lemma. step towards coprime_matching_of_exponent_lt_prime

The value attached to prime p in row t of the Vandermonde-type matrix for the coprime matching problem: if p divides the common difference b it is the prime power p^t, otherwise it is ζ^{a+bt} − 1 for the supplied p-th root of unity ζ.
-/

/-- Row entry value at prime p and row t: p^t when p ∣ b, and z_p^(a+bt) - 1 otherwise. -/
noncomputable def coprime_matching_row_value (a b : Nat) (z : Nat → Complex) (p t : Nat) : Complex := if p ∣ b then (p : Complex) ^ t else (z p) ^ (a + b * t) - 1
