import AFTD.Prelude

/-!
# poset_down_sets

Topic: algorithms   Node: d6815175d1d0

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

Given a natural number n, a partial order P on Fin n, and a natural number k, the finite set (as a Finset of Finsets) of all down-sets of Fin n of cardinality k with respect to P.
-/

/-- The finite set of down-sets of cardinality k in a partial order on Fin n. -/
noncomputable def poset_down_sets (n : ℕ) (P : PartialOrder (Fin n)) (k : ℕ) : Finset (Finset (Fin n)) := open scoped Classical in
  letI := P
  Finset.filter (fun L => L.card = k ∧ IsLowerSet (L : Set (Fin n))) Finset.univ
