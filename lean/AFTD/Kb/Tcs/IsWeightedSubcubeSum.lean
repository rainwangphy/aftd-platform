import AFTD.Prelude

/-!
# is_weighted_subcube_sum

Topic: proof_complexity   Node: 64a3b8912174

Provenance: helper lemma. step towards op_983_exists_asymptotic_separation_witness

A function h on the n-dimensional Boolean cube is a sum of s nonnegative weighted subcube indicators if h τ = ∑_{j : Fin s} (w_j if τ agrees with the partial assignment (S_j, a_j) on every coordinate of S_j, and 0 otherwise), for some nonnegative weights w_j and some partial assignments given by a fixed coordinate set S_j and fixed values a_j. This is the canonical form of a bounded-bias depth-three AMC proof: each bounded-bias rank-one product is a nonnegative multiple of a subcube indicator.
-/

/-- `h` is a sum of `s` nonnegative multiples of subcube indicators of the n-cube. -/
def is_weighted_subcube_sum {n : ℕ} (h : (Fin n → Bool) → ℝ) (s : ℕ) : Prop := ∃ w : Fin s → ℝ, (∀ j, 0 ≤ w j) ∧
    ∃ (S : Fin s → Finset (Fin n)) (a : Fin s → Fin n → Bool),
      ∀ τ : Fin n → Bool,
        h τ = ∑ j : Fin s, (if ∀ i ∈ S j, τ i = a j i then w j else 0)
