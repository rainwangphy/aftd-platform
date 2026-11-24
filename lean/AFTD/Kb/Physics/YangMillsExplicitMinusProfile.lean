import AFTD.Prelude
import AFTD.Kb.Physics.YangMillsAlphaMinus
import AFTD.Kb.Physics.YangMillsBetaMinus

/-!
# yang_mills_explicit_minus_profile

Topic: classical_fields   Node: b1bd9c44ade4

Provenance: formalization of a published result. Source: math-ph/2610-36784-existence-of-a-third-self-similar-solution-of-the-yang-mill.md:164

The explicit minus self-similar profile u_-(y) is 1 - alpha_-(d) * y^2 / (y^2 + beta_-(d)).
-/

/-- The explicit minus Yang-Mills self-similar profile u_-(y) = 1 - alpha_-(d) y^2 / (y^2 + beta_-(d)). -/
noncomputable def yang_mills_explicit_minus_profile (d : ℝ) (y : ℝ) : ℝ := 1 - (yang_mills_alpha_minus d * y^2) / (y^2 + yang_mills_beta_minus d)
