import AFTD.Prelude
import AFTD.Kb.Tcs.AdditiveBasisThreshold
import AFTD.Kb.Tcs.ExistsSubmultisetCardEq
import AFTD.Kb.Tcs.IsRegularSequenceOfLe
import AFTD.Kb.Tcs.IsAdditiveBasisOfLe
import AFTD.Kb.Tcs.IsAdditiveBasis
import AFTD.Kb.Tcs.IsRegularSequence

/-!
# additive_basis_threshold_le_of_card_eq

Topic: combinatorics   Node: be7fa5102bb1

Provenance: helper lemma. step towards additive_basis_bound_cp_cnp_conjecture

To bound the additive basis threshold c_0(G) ≤ m, it suffices to show that every regular sequence S over G of cardinality exactly m is an additive basis.
-/

/-- To bound the additive basis threshold c_0(G) ≤ m, it suffices to show that every regular sequence S over G of cardinality exactly m is an additive basis. -/
theorem additive_basis_threshold_le_of_card_eq {G : Type*} [AddCommGroup G] (m : ℕ) (h : ∀ S : Multiset G, IsRegularSequence S → S.card = m → IsAdditiveBasis S) : additive_basis_threshold G ≤ m := by
  unfold additive_basis_threshold
  apply Nat.sInf_le
  intro S hS hm
  obtain ⟨T, hTS, hTcard⟩ := exists_submultiset_card_eq S m hm
  have hTreg : IsRegularSequence T := is_regular_sequence_of_le hS hTS
  have hTbasis : IsAdditiveBasis T := h T hTreg hTcard
  exact is_additive_basis_of_le hTbasis hTS
