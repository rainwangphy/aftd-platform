import AFTD.Prelude

/-!
# dual_melas_is_non_degenerate

Topic: information   Node: 7c8dbc53069e

Provenance: formalization of a published result. Source: arXiv:2610.38017 Definition 3

A binary polynomial f is non-degenerate with respect to α if neither α nor α⁻¹ is a root of f under polynomial evaluation.
-/

/-- Predicate that neither α nor α⁻¹ is a root of f. -/
def dual_melas_is_non_degenerate {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (α : F) (f : Polynomial (ZMod 2)) : Prop := Polynomial.aeval α f ≠ 0 ∧ Polynomial.aeval α⁻¹ f ≠ 0
