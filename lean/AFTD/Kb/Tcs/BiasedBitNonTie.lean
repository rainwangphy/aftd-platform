import AFTD.Prelude

/-!
# biased_bit_non_tie

Topic: information   Node: 01c2d7142c3a

Provenance: formalization of a published result. Source: arXiv:2611.16066 Cor 5.9

For a bias parameter p : ℝ, biased_bit_non_tie p is the proposition that for all natural numbers j and k with 1 ≤ j and j < k, 2 * a ^ j ≠ 1 + a ^ k, where a = (1 - p) / p.
-/

/-- Predicate asserting that the likelihood ratio a = (1 - p) / p satisfies the non-tie condition 2 * a^j ≠ 1 + a^k for all 1 ≤ j < k. -/
def biased_bit_non_tie (p : ℝ) : Prop := let a := (1 - p) / p
  ∀ (j k : ℕ), 1 ≤ j → j < k → 2 * a ^ j ≠ 1 + a ^ k
