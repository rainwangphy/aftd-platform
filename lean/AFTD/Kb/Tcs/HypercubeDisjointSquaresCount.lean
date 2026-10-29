import AFTD.Prelude
import AFTD.Kb.Tcs.IsHypercubeSquare

/-!
# hypercube_disjoint_squares_count

Topic: combinatorics   Node: 037f8fd18cc8

Provenance: formalization of a published result. Source: arXiv:2610.36461 Section 2.1

The count F_5 is the number of squares in Q_n that contain no vertex of S.
-/

/-- The number of squares in Q_n that are completely disjoint from S. -/
noncomputable def hypercube_disjoint_squares_count (n : ℕ) (S : Finset (Fin n → Bool)) : ℕ :=
  open scoped Classical in
  (Finset.univ.powerset.filter (fun sq => is_hypercube_square n sq ∧ Disjoint sq S)).card
