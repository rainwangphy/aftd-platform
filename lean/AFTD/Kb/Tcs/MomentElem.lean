import AFTD.Prelude

/-!
# moment_elem

Topic: combinatorics   Node: 65b5e43e7d10

Provenance: helper lemma. step towards infinite_bh_set_upper_density_eq_one_div_h

The `ℓ`-digit positional encoding of the truncated finite-field moment curve: for integers `h`, `q`, `ℓ` and a residue `a`, the base-`h*q` number whose `j`-th digit (counted from the least significant, `0 ≤ j < ℓ`) is `a^(j+1) mod q`. With `ℓ = h` this is the paper's `f_q(a) = Σ_{j=1}^{h} [a^j]_q (hq)^{h-j}`.
-/

/-- Positional (base `h*q`) encoding of the truncated moment curve `a ↦ (a, a², …, a^ℓ)`. -/
def moment_elem (h q ℓ a : ℕ) : ℕ := ∑ j ∈ Finset.range ℓ, (a ^ (j + 1) % q) * (h * q) ^ (ℓ - 1 - j)
