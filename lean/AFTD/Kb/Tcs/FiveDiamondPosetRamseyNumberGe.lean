import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset
import AFTD.Kb.Tcs.PosetRamseyNumber
import AFTD.Kb.Tcs.ExistsPosetRamseyPropertyDiamond
import AFTD.Kb.Tcs.FiveDiamondRamseyPropertyFourMulLe
import AFTD.Kb.Tcs.PosetRamseyProperty

/-!
# five_diamond_poset_ramsey_number_ge

Topic: combinatorics   Node: 8a565649af4a

Provenance: formalization of a published result. Source: arXiv:2610.20545, The k-color poset Ramsey number of the diamond is 2k, Section 1

For every natural number k with 1 ≤ k, the k-color poset Ramsey number of the 5-diamond DiamondPoset 5 is at least 4 * k.
-/

/-- For any k >= 1, the k-color poset Ramsey number of DiamondPoset 5 is at least 4 * k. -/
theorem five_diamond_poset_ramsey_number_ge (k : ℕ) (hk : 1 ≤ k) : 4 * k ≤ poset_ramsey_number (DiamondPoset 5) k := by
  obtain ⟨d₀, h₀⟩ := exists_poset_ramsey_property_diamond 5 k (by norm_num) hk
  have hmem : poset_ramsey_number (DiamondPoset 5) k ∈ {d | poset_ramsey_property (DiamondPoset 5) k d} :=
    Nat.sInf_mem ⟨d₀, h₀⟩
  exact five_diamond_ramsey_property_four_mul_le k _ hk hmem
