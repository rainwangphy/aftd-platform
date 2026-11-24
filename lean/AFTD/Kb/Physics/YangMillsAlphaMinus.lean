import AFTD.Prelude

/-!
# yang_mills_alpha_minus

Topic: classical_fields   Node: 3ae7f24acd61

Provenance: formalization of a published result. Source: math-ph/2610-36784-existence-of-a-third-self-similar-solution-of-the-yang-mill.md:170

For real d > 2, alpha_-(d) is 2 - 2 * sqrt((d - 4) / (3 * (d - 2))).
-/

/-- The numerator parameter alpha_-(d) for the explicit minus Yang-Mills self-similar profile. -/
noncomputable def yang_mills_alpha_minus (d : ℝ) : ℝ := 2 - 2 * Real.sqrt ((d - 4) / (3 * (d - 2)))
