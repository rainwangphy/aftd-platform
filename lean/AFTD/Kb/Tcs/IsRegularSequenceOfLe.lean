import AFTD.Prelude
import AFTD.Kb.Tcs.IsRegularSequence

/-!
# is_regular_sequence_of_le

Topic: combinatorics   Node: 661ea3659891

Provenance: helper lemma. step towards additive_basis_bound_cp_cnp_conjecture

Any submultiset of a regular sequence over an additive commutative group is also a regular sequence.
-/

/-- Any submultiset of a regular sequence over an additive commutative group is also a regular sequence. -/
theorem is_regular_sequence_of_le {G : Type*} [AddCommGroup G] {S T : Multiset G} (hS : IsRegularSequence S) (hTS : T ≤ S) : IsRegularSequence T := by
  classical
  intro H hH
  exact le_trans (Multiset.card_le_card (Multiset.filter_le_filter (fun x => x ∈ H) hTS)) (hS H hH)
