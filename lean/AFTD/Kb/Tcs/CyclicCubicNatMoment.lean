import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicFamilyNat

/-!
# cyclic_cubic_nat_moment

Topic: quantum   Node: e3a74d4db2a7

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The moment at the Nat level: the number of members of cyclic_cubic_family_nat n that contain T.
-/

/-- Number of Nat-level family members containing T. -/
def cyclic_cubic_nat_moment (n : ℕ) (T : Finset ℕ) : ℕ := ((cyclic_cubic_family_nat n).filter (fun Y => T ⊆ Y)).card
