import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondPosetRamseyProperty
import AFTD.Kb.Tcs.PosetRamseyProperty
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset

/-!
# exists_poset_ramsey_property_diamond

Topic: combinatorics   Node: f89873e65690

Provenance: helper lemma. step towards five_diamond_poset_ramsey_number_ge

For j ≥ 2 and k ≥ 1 the k-colour poset Ramsey property for the j-diamond is satisfied by some d: there is a d such that every colouring of the subsets of Fin d with k colours contains a monochromatic induced copy of DiamondPoset j (i.e. the set of such d is nonempty, so the k-colour poset Ramsey number of the j-diamond is finite).
-/

/-- Nonemptiness of the set of d satisfying the k-colour j-diamond Ramsey property, an immediate repackaging of the paper's upper bound. -/
theorem exists_poset_ramsey_property_diamond (j k : ℕ) (hj : 2 ≤ j) (hk : 1 ≤ k) :
    ∃ d : ℕ, poset_ramsey_property (DiamondPoset j) k d := by
  exact ⟨j * k, diamond_poset_ramsey_property j k hj hk⟩
