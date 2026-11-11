import AFTD.Prelude

/-!
# f2_real_character_values

Topic: quantum_mechanics   Node: c16d25e9c318

Provenance: helper lemma. Binary character infrastructure for the OP-827 supported-kernel entropy reduction.

Every real-valued additive character of a binary vector space takes only the values one and minus one.
-/

theorem f2_real_character_values {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (χ : AddChar M ℝ) (x : M) : χ x = 1 ∨ χ x = -1 := by
  have hx : x + x = 0 := by
    calc
      x + x = (2 : ZMod 2) • x := by simp [two_smul]
      _ = 0 := by
        have htwo : (2 : ZMod 2) = 0 := by decide
        rw [htwo, zero_smul]
  have hsq : χ x * χ x = 1 := by
    simpa [hx] using (AddChar.map_add_eq_mul χ x x).symm
  exact mul_self_eq_one_iff.mp hsq
