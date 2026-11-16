import AFTD.Prelude

/-!
# low_half_mul_three_targets

Topic: circuits   Node: 48d70d1dec38

Provenance: formalization of a published result. Source: arXiv:2611.15992 Section 2

The set of three Boolean functions of type Set ((Fin 6 → ZMod 2) → ZMod 2) representing the output bits z₀, z₁, z₂ of the 3-bit low-half multiplier on input x : Fin 6 → ZMod 2, given by x ↦ x 0 * x 3, x ↦ x 0 * x 4 + x 1 * x 3, and x ↦ x 0 * x 5 + x 1 * x 4 + x 2 * x 3 + x 0 * x 1 * x 3 * x 4.
-/

/-- The set of target Boolean functions {z₀, z₁, z₂} of the three-bit low-half multiplier. -/
def low_half_mul_three_targets : Set ((Fin 6 → ZMod 2) → ZMod 2) := { (fun x => x 0 * x 3), (fun x => x 0 * x 4 + x 1 * x 3), (fun x => x 0 * x 5 + x 1 * x 4 + x 2 * x 3 + x 0 * x 1 * x 3 * x 4) }
