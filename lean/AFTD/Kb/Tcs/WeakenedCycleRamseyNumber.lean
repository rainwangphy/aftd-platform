import AFTD.Prelude
import AFTD.Kb.Tcs.WeakenedCycleRamseyProperty

/-!
# weakened_cycle_ramsey_number

Topic: combinatorics   Node: d4be212ba273

Provenance: formalization of a published result. Source: arXiv:2611.11187, Section 1

The weakened multicolour Ramsey number weakened_cycle_ramsey_number t ℓ of a cycle C_ℓ is the least integer n such that every t-edge-colouring of K_n contains a cycle of length ℓ using at most t - 1 colours.
-/

/-- The (t-1)-chromatic Ramsey number R^t_{t-1}(C_ℓ) of the cycle of length ℓ. -/
noncomputable def weakened_cycle_ramsey_number (t ℓ : ℕ) : ℕ := sInf {n : ℕ | weakened_cycle_ramsey_property t ℓ n}
