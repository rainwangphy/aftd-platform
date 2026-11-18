import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumIndexSets

/-!
# zero_sum_incidence_identity

Topic: combinatorics   Node: d5d46bd8c284

Provenance: formalization of a published result. Source: arXiv:2611.20197

Given an additive commutative group G, a natural number N, a sequence U : Fin N → G, an integer t : ℕ, and a commutative ring R, a family of weights c : zero_sum_index_sets U → R is an I_t-identity if the sum of c E over all E : zero_sum_index_sets U equals 1, and for every nonempty subset J : Finset (Fin N) with 1 ≤ J.card and J.card ≤ t, the sum of c E over all zero-sum sets E containing J equals 0.
-/

open Classical in
/-- An I_t-identity for U over R is a family of weights (c_E) on the zero-sum sets summing to 1 whose moments of size 1 to t vanish. -/
def zero_sum_incidence_identity {G : Type*} [AddCommGroup G] {N : ℕ} (U : Fin N → G)
    (t : ℕ) {R : Type*} [CommRing R] (c : zero_sum_index_sets U → R) : Prop :=
  (∑ E : zero_sum_index_sets U, c E = 1) ∧
  (∀ J : Finset (Fin N), 1 ≤ J.card → J.card ≤ t →
    ∑ E : zero_sum_index_sets U, (if J ⊆ (E : Finset (Fin N)) then c E else 0) = 0)
