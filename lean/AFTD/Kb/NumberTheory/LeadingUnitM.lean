import AFTD.Prelude
import AFTD.Kb.NumberTheory.LeadingUnitA

/-!
# leading_unit_m

Topic: elementary_number_theory   Node: eb2411e9ff43

Provenance: formalization of a published result. Source: arXiv:2611.10200, eq. (1.5)

The unrounded completeness threshold M_{g,k} = (a_{g+k}^{(g)} + 1) / 2^g for positive integers g and k.
-/

/-- The unrounded completeness threshold M_{g,k} = (a_{g+k}^{(g)} + 1) / 2^g. -/
noncomputable def leading_unit_m (g k : ℕ) : ℚ :=
  (leading_unit_a g (g + k) + 1) / (2 : ℚ) ^ g
