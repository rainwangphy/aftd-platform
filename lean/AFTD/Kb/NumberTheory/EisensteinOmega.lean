import AFTD.Prelude

/-!
# eisensteinOmega

Topic: elementary_number_theory   Node: be5fd18ee3c3

Provenance: formalization of a published result. Source: scout/2611-01243-halving-partitions-and-hyperbinary-expansions.md:1188

The primitive cube root of unity ω = (-1 + √(-3))/2 in the complex numbers.
-/

/-- The primitive cube root of unity ω = (-1 + √(-3))/2 in ℂ. -/
noncomputable def eisensteinOmega : ℂ := (-1 + Complex.I * Real.sqrt 3) / 2
