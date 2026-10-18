import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy

/-!
# mixed_ramsey_property

Topic: combinatorics   Node: 982f633405b4

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

mixed_ramsey_property j a b d asserts that every colouring of the subsets of Fin d with a + b colours has a monochromatic induced copy of the j-diamond D_j in one of the first a colours, or a monochromatic induced copy of F_j (a maximum element over an antichain of size j) in one of the last b colours.
-/

/-- The multicolour Ramsey property in which the first a colours are assigned the j-diamond and the last b colours the poset F_j (the paper's f(a,b) statement). -/
def mixed_ramsey_property (j a b d : ℕ) : Prop := ∀ χ : Finset (Fin d) → Fin (a + b),
    (∃ col : Fin a, has_monochromatic_diamond_copy j d (Fin.castAdd b col) χ) ∨
    (∃ col : Fin b, has_monochromatic_fan_copy j d (Fin.natAdd a col) χ)
