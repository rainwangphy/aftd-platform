import AFTD.Prelude

/-!
# energy_filter_centered_binomial_weight

Topic: statistical_mechanics   Node: 832c87642d75

Provenance: original. Related work: Zero-extended centered binomial weights for OP-892; experiment 26245.

For a natural k and integer s, the centered binomial weight is the real ratio choose(2k,k+s)/choose(2k,k) when −k ≤ s ≤ k, and is zero outside that interval; the integer index k+s is converted to a natural only within the interval.
-/

noncomputable def energy_filter_centered_binomial_weight (k : ℕ) (s : ℤ) : ℝ := if -(k : ℤ) ≤ s ∧ s ≤ (k : ℤ) then (Nat.choose (2 * k) ((k : ℤ) + s).toNat : ℝ) / (Nat.choose (2 * k) k : ℝ) else 0
