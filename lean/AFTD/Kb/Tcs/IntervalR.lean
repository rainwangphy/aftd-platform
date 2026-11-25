import AFTD.Prelude

/-!
# interval_r

Topic: learning   Node: 20e00731f6f6

Provenance: formalization of a published result. Source: arXiv:2611.28727 Section 9, before Lemma 29

The sequence R : ℕ → ℚ of rational numbers, defined by R 0 = 0, R 1 = 0, and for l = n + 2, R l = 1 - 1 / (2^(l - 1) : ℚ) + (R (l / 2) + R ((l + 1) / 2)) / 2.
-/

/-- The sequence R(ℓ) defined by R(1) = 0 and R(ℓ) = 1 - 2^(1 - ℓ) + (1/2)(R(⌊ℓ/2⌋) + R(⌈ℓ/2⌉)) for ℓ ≥ 2. -/
def interval_r : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    let l := n + 2
    1 - (1 : ℚ) / (2 ^ (l - 1) : ℚ) + (interval_r (l / 2) + interval_r ((l + 1) / 2)) / 2
termination_by l => l
