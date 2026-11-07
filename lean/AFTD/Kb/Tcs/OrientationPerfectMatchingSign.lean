import AFTD.Prelude

/-!
# orientation_perfect_matching_sign

Topic: combinatorics   Node: c770f484efdd

Provenance: formalization of a published result. Source: arXiv:2611.00468 (The symbolic pfaffian method I), Section 1.1, the sign sign_D(M) of a perfect matching (vertices enumerated as Fin n; value 0 when no listing exists)

For n : ℕ, a simple graph G : SimpleGraph (Fin n) (implicit), a digraph D : Digraph (Fin n) and a subgraph M : G.Subgraph, the integer sign of M in D: if some permutation π : Equiv.Perm (Fin n) lists the edges of M in consecutive pairs, oriented by D -- for every natural j with 2j+1 < n, M.Adj (π (2j)) (π (2j+1)) and D.Adj (π (2j)) (π (2j+1)) -- then it is the sign of such a permutation (one chosen by Classical.choice), as the integer 1 or -1; otherwise it is 0.
-/

open Classical in
/-- The sign of a perfect matching `M` in an orientation `D` of a graph on `Fin n`. -/
noncomputable def orientation_perfect_matching_sign {n : ℕ} {G : SimpleGraph (Fin n)}
    (D : Digraph (Fin n)) (M : G.Subgraph) : ℤ :=
  if h : ∃ π : Equiv.Perm (Fin n), ∀ (j : ℕ) (hj : 2 * j + 1 < n),
      M.Adj (π ⟨2 * j, by omega⟩) (π ⟨2 * j + 1, hj⟩) ∧ D.Adj (π ⟨2 * j, by omega⟩) (π ⟨2 * j + 1, hj⟩)
  then ((Equiv.Perm.sign h.choose : ℤˣ) : ℤ) else 0
