import AFTD.Prelude

/-!
# f2_value_cases

Topic: quantum_mechanics   Node: a794b13f3d95

Provenance: helper lemma. Binary character infrastructure for the OP-827 supported-kernel entropy reduction.

Each element of the two-element field equals zero or one.
-/

theorem f2_value_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
