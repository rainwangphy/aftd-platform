import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdditiveBasis

/-!
# is_additive_basis_of_le

Topic: combinatorics   Node: 123fa8ccb1b9

Provenance: helper lemma. step towards additive_basis_bound_cp_cnp_conjecture

If a submultiset T of S is an additive basis of an additive commutative group G, then S is also an additive basis of G.
-/

/-- If a submultiset T of S is an additive basis of an additive commutative group G, then S is also an additive basis of G. -/
theorem is_additive_basis_of_le {G : Type*} [AddCommGroup G] {S T : Multiset G} (hT : IsAdditiveBasis T) (hTS : T ≤ S) : IsAdditiveBasis S := by
  intro g
  rcases hT g with ⟨U, hUT, hU0, hUsum⟩
  exact ⟨U, hUT.trans hTS, hU0, hUsum⟩
