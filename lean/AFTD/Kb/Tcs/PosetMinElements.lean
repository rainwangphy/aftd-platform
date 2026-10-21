import AFTD.Prelude

/-!
# poset_min_elements

Topic: algorithms   Node: 2802bfc4b4a4

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

Given a natural number n, a partial order P on Fin n, and a finite subset S of Fin n, the subset of S (as a Finset) consisting of all elements minimal in S with respect to P.
-/

/-- The set of minimal elements of a subset in a partial order on Fin n. -/
noncomputable def poset_min_elements {n : ℕ} (P : PartialOrder (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) := open scoped Classical in
  letI := P
  Finset.filter (fun x => ∀ y ∈ S, y ≤ x → y = x) S
