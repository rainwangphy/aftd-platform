import AFTD.Prelude

/-!
# yang_mills_beta_minus

Topic: classical_fields   Node: fa4a00fad9f1

Provenance: formalization of a published result. Source: math-ph/2610-36784-existence-of-a-third-self-similar-solution-of-the-yang-mill.md:170

For real d >= 4, beta_-(d) is (2 * (d - 4) - sqrt(3 * (d - 2) * (d - 4))) / 3.
-/

/-- The denominator parameter beta_-(d) for the explicit minus Yang-Mills self-similar profile. -/
noncomputable def yang_mills_beta_minus (d : ℝ) : ℝ := (2 * (d - 4) - Real.sqrt (3 * (d - 2) * (d - 4))) / 3
