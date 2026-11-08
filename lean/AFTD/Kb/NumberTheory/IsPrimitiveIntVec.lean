import AFTD.Prelude

/-!
# is_primitive_int_vec

Topic: elementary_number_theory   Node: e8ecce225413

Provenance: formalization of a published result. Source: arXiv:2610.37711, Section 4

An integer vector is primitive if every natural number dividing all of its coordinates divides 1.
-/

/-- An integer vector is primitive if every natural number dividing all coordinates divides 1. -/
def is_primitive_int_vec (n : ℕ) (v : Fin n → ℤ) : Prop := ∀ d : ℕ, (∀ i, (d : ℤ) ∣ v i) → d ∣ 1
