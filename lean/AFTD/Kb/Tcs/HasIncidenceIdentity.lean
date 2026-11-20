import AFTD.Prelude

/-!
# HasIncidenceIdentity

Topic: combinatorics   Node: 522e3a80e1f5

Provenance: formalization of a published result. Source: arXiv:2611.20197, Definition 1.3

An abelian group Q has an incidence identity of degree t over R for sequences of length L(t) if every sequence of L(t) elements in Q admits weights c on its non-empty zero sets summing to 1 such that for every non-empty set of positions J of size at most t, the weights on zero sets containing J sum to 0.
-/

/-- Every sequence of length L(t) over Q has an incidence identity of degree t over R. -/
def HasIncidenceIdentity (Q : Type*) [AddCommGroup Q] (L : ℕ → ℕ) (t : ℕ) (R : Type*) [CommRing R] : Prop := ∀ (u : Fin (L t) → Q), ∃ (c : Finset (Fin (L t)) → R),
    (∀ E, c E ≠ 0 → E.Nonempty ∧ ∑ j ∈ E, u j = 0) ∧
    (∑ E ∈ (Finset.univ : Finset (Fin (L t))).powerset, c E = 1) ∧
    ∀ J : Finset (Fin (L t)), 1 ≤ J.card ∧ J.card ≤ t →
      ∑ E ∈ (Finset.univ : Finset (Fin (L t))).powerset.filter (fun E => J ⊆ E), c E = 0
