import AFTD.Prelude
import AFTD.Kb.Tcs.OrientationPerfectMatchingSign

/-!
# orientation_tuple_is_pfaffian

Topic: combinatorics   Node: 42a5ca2c16e3

Provenance: formalization of a published result. Source: arXiv:2611.00468 (The symbolic pfaffian method I), Section 1.1, pfaffian k-orientation (the system sign_D x = 1 solved over ℝ)

For n K : ℕ, a simple graph G : SimpleGraph (Fin n) and a K-tuple of digraphs D : Fin K → Digraph (Fin n): there is x : Fin K → ℝ such that for every perfect matching M of G (M : G.Subgraph with M.IsPerfectMatching), ∑ over j : Fin K of (orientation_perfect_matching_sign (D j) M : ℝ) * x j = 1; that is, the signature system sign_D x = 1 has a real solution.
-/

/-- A tuple of orientations is pfaffian when its signature system has a real solution. -/
def orientation_tuple_is_pfaffian {n K : ℕ} (G : SimpleGraph (Fin n))
    (D : Fin K → Digraph (Fin n)) : Prop :=
  ∃ x : Fin K → ℝ, ∀ M : G.Subgraph, M.IsPerfectMatching →
    ∑ j, (orientation_perfect_matching_sign (D j) M : ℝ) * x j = 1
