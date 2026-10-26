import AFTD.Prelude
import AFTD.Kb.Tcs.IsRegularSequence
import AFTD.Kb.Tcs.IsAdditiveBasis

/-!
# additive_basis_threshold

Topic: combinatorics   Node: 725e7d68a6c9

Provenance: formalization of a published result. Source: scout/2610-13103-additive-bases-and-the-zero-sum-invariant-mathsf-n-g-for-gr.md:73

The additive basis threshold c_0(G) of an additive commutative group G is the minimal integer l, defined as the infimum of the set of natural numbers l such that every regular multiset S : Multiset G over G with S.card ≥ l satisfies IsAdditiveBasis S.
-/

/-- The minimal integer l such that every regular sequence S over G with |S| ≥ l is an additive basis. -/
noncomputable def additive_basis_threshold (G : Type*) [AddCommGroup G] : ℕ := sInf {l : ℕ | ∀ S : Multiset G, IsRegularSequence S → l ≤ S.card → IsAdditiveBasis S}
