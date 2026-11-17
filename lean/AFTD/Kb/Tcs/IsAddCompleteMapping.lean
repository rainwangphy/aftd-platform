import AFTD.Prelude

/-!
# is_add_complete_mapping

Topic: combinatorics   Node: b9822b685394

Provenance: formalization of a published result. Source: arXiv:2611.18059 Section 1

A function φ from an additive group Γ to itself is an additive complete mapping if φ is bijective and the map x ↦ x + φ(x) is bijective.
-/

/-- An additive complete mapping of an additive group is a bijection φ such that x ↦ x + φ(x) is bijective. -/
def is_add_complete_mapping {Γ : Type*} [AddGroup Γ] (φ : Γ → Γ) : Prop := Function.Bijective φ ∧ Function.Bijective fun x => x + φ x
