import AFTD.Prelude

/-!
# poset_max_elements

Topic: algorithms   Node: ae3653285244

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

Given a natural number n, a partial order P on Fin n, and a finite subset S of Fin n, the subset of S (as a Finset) consisting of all elements maximal in S with respect to P.
-/

/-- The set of maximal elements of a subset in a partial order on Fin n. -/
noncomputable def poset_max_elements {n : ℕ} (P : PartialOrder (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) := open scoped Classical in
  letI := P
  Finset.filter (fun x => ∀ y ∈ S, x ≤ y → y = x) S
