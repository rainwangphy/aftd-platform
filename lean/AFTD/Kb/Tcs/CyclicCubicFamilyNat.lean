import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicFamilyNatA
import AFTD.Kb.Tcs.CyclicCubicFamilyNatB
import AFTD.Kb.Tcs.CyclicCubicFamilyNatC

/-!
# cyclic_cubic_family_nat

Topic: quantum   Node: d6b7468e4be2

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The Nat-level model of cyclic_cubic_family: the union of the ten group-A boundary parities, the 2(n-4) group-B running parities and the three group-C span parities.
-/

/-- Nat-level model of the cyclic cubic family: exactly the three groups A, B, C. -/
def cyclic_cubic_family_nat (n : ℕ) : Finset (Finset ℕ) := cyclic_cubic_family_nat_A n ∪ cyclic_cubic_family_nat_B n ∪ cyclic_cubic_family_nat_C n
