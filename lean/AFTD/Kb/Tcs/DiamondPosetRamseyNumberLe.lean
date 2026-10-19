import AFTD.Prelude
import AFTD.Kb.Tcs.DiamondPoset
import AFTD.Kb.Tcs.InstPartialOrderDiamondPoset
import AFTD.Kb.Tcs.PosetRamseyNumber
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.MixedRamseyProperty
import AFTD.Kb.Tcs.MonochromaticCopyDefSanity
import AFTD.Kb.Tcs.ExistsHittingSetOfNoLargeAntichain
import AFTD.Kb.Tcs.FanRamseyBound
import AFTD.Kb.Tcs.MixedDiamondFanRamseyBound
import AFTD.Kb.Tcs.OrderEmbeddingOfDiamondCopy
import AFTD.Kb.Tcs.DiamondPosetRamseyProperty
import AFTD.Kb.Tcs.PosetRamseyProperty

/-!
# diamond_poset_ramsey_number_le

Topic: combinatorics   Node: b66895b4a65c

Provenance: formalization of a published result. Source: arXiv:2610.20545, The k-color poset Ramsey number of the diamond is 2k, Theorem 2

For all natural numbers j ≥ 2 and k ≥ 1, the k-color poset Ramsey number of the j-diamond DiamondPoset j is at most j * k.
-/

/-- For any j >= 2 and k >= 1, the k-color poset Ramsey number of DiamondPoset j is at most j * k. -/
theorem diamond_poset_ramsey_number_le (j : ℕ) (hj : 2 ≤ j) (k : ℕ) (hk : 1 ≤ k) : poset_ramsey_number (DiamondPoset j) k ≤ j * k := by
  exact Nat.sInf_le (diamond_poset_ramsey_property j k hj hk)
