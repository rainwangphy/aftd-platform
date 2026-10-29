import AFTD.Prelude
import AFTD.Kb.Tcs.SubsequenceSums

/-!
# mem_subsequence_sums

Topic: combinatorics   Node: 46cb9115dbfb

Provenance: helper lemma. arXiv:2610.35819 Section 8

Given a natural number n, an additive commutative monoid G with decidable equality, a multiset S over G, and an element g of G, g belongs to the finite set subsequence_sums n S if and only if there exists a submultiset U ≤ S with card U = n and sum U = g.
-/

/-- Membership in subsequence_sums n S is equivalent to the existence of a length-n submultiset with sum g. -/
theorem mem_subsequence_sums {n : ℕ} {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Multiset G) (g : G) :
    g ∈ subsequence_sums n S ↔ ∃ U ≤ S, U.card = n ∧ U.sum = g := by
  unfold subsequence_sums
  rw [Multiset.mem_toFinset, Multiset.mem_map]
  simp only [Multiset.mem_filter, Multiset.mem_powerset]
  exact ⟨fun ⟨U, ⟨hU, hc⟩, hs⟩ => ⟨U, hU, hc, hs⟩,
    fun ⟨U, hU, hc, hs⟩ => ⟨U, ⟨hU, hc⟩, hs⟩⟩
