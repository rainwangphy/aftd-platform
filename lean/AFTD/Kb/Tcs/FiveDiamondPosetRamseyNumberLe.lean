import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset
import AFTD.Kb.Tcs.PosetRamseyNumber
import AFTD.Kb.Tcs.DiamondPosetRamseyNumberLe

/-!
# five_diamond_poset_ramsey_number_le

Topic: combinatorics   Node: c8f48394a2ee

Provenance: formalization of a published result. Source: arXiv:2610.20545, The k-color poset Ramsey number of the diamond is 2k, Theorem 2

For every natural number k with 1 ≤ k, the k-color poset Ramsey number of the 5-diamond DiamondPoset 5 is at most 5 * k.
-/

/-- For any k >= 1, the k-color poset Ramsey number of DiamondPoset 5 is at most 5 * k. -/
theorem five_diamond_poset_ramsey_number_le (k : ℕ) (hk : 1 ≤ k) : poset_ramsey_number (DiamondPoset 5) k ≤ 5 * k := diamond_poset_ramsey_number_le 5 (by decide) k hk
