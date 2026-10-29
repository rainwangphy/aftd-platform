import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHypercube

/-!
# hypercube_degree_count

Topic: combinatorics   Node: 99bab0069277

Provenance: formalization of a published result. Source: arXiv:2610.36461 Section 2

The degree count y_m is the number of vertices x in the complement of S having exactly m neighbors in S.
-/

/-- The number of vertices outside S with exactly m neighbors in S. -/
noncomputable def hypercube_degree_count (n : ℕ) (S : Finset (Fin n → Bool)) (m : ℕ) : ℕ :=
  open scoped Classical in
  ((Finset.univ \ S).filter (fun x => ((simple_graph_hypercube n).neighborFinset x ∩ S).card = m)).card
