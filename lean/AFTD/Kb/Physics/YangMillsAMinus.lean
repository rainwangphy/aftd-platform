import AFTD.Prelude
import AFTD.Kb.Physics.YangMillsAlphaMinus
import AFTD.Kb.Physics.YangMillsBetaMinus

/-!
# yang_mills_a_minus

Topic: classical_fields   Node: ea796c1acf73

Provenance: formalization of a published result. Source: math-ph/2610-36784-existence-of-a-third-self-similar-solution-of-the-yang-mill.md:170

For real d, a_-(d) is the quotient alpha_-(d) / beta_-(d).
-/

/-- The shooting parameter a_-(d) = alpha_-(d) / beta_-(d) for the explicit minus self-similar profile. -/
noncomputable def yang_mills_a_minus (d : ℝ) : ℝ := yang_mills_alpha_minus d / yang_mills_beta_minus d
