import AFTD.Prelude
import AFTD.Kb.Tcs.OrientationTupleIsPfaffian
import AFTD.Kb.Tcs.OrientationPerfectMatchingSign
import AFTD.Kb.Tcs.IsGraphOrientation
import AFTD.Kb.Tcs.PmOneRowsDifferInHalfExistsSolution
import AFTD.Kb.Tcs.OrientationPerfectMatchingSignEqOneOrNegOne

/-!
# orientation_tuple_is_pfaffian_of_rows_differ_in_half

Topic: combinatorics   Node: 5c8a7d2d669c

Provenance: formalization of a published result. Source: arXiv:2611.00468 (The symbolic pfaffian method I), Lemma 2.1 (vertices Fin n; 'different rows' read as perfect matchings with different sign vectors; the solution is over ℝ; k ≥ 1 explicit)

Let k ≥ 1, let G be a simple graph on Fin n and let D : Fin (2k) → Digraph (Fin n) be a 2k-tuple of orientations of G (is_graph_orientation G (D j) for every j). Suppose that any two perfect matchings M, N of G whose sign vectors (orientation_perfect_matching_sign (D j) M)_j and (orientation_perfect_matching_sign (D j) N)_j are different differ in exactly k coordinates j. Then D is pfaffian (orientation_tuple_is_pfaffian G D).
-/

theorem orientation_tuple_is_pfaffian_of_rows_differ_in_half {n k : ℕ} (hk : 1 ≤ k)
    (G : SimpleGraph (Fin n)) (D : Fin (2 * k) → Digraph (Fin n))
    (hD : ∀ j, is_graph_orientation G (D j))
    (hrows : ∀ M N : G.Subgraph, M.IsPerfectMatching → N.IsPerfectMatching →
      (fun j => orientation_perfect_matching_sign (D j) M) ≠
        (fun j => orientation_perfect_matching_sign (D j) N) →
      (Finset.univ.filter fun j => orientation_perfect_matching_sign (D j) M ≠
        orientation_perfect_matching_sign (D j) N).card = k) :
    orientation_tuple_is_pfaffian G D := by
  classical
  have hfin : Finite G.Subgraph :=
    Finite.of_injective (fun H : G.Subgraph => (H.verts, H.Adj)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact SimpleGraph.Subgraph.ext h.1 h.2)
  obtain ⟨x, hx⟩ := pm_one_rows_differ_in_half_exists_solution hk
    (ι := {M : G.Subgraph // M.IsPerfectMatching})
    (fun M j => (orientation_perfect_matching_sign (D j) M.1 : ℝ))
    (fun M j => by
      rcases orientation_perfect_matching_sign_eq_one_or_neg_one G (D j) (hD j) M.1 M.2 with h | h
      · left; simp [h]
      · right; simp [h])
    (fun M N hne => by
      have hne' : (fun j => orientation_perfect_matching_sign (D j) M.1) ≠
          (fun j => orientation_perfect_matching_sign (D j) N.1) := by
        intro h
        apply hne
        funext j
        simp only [congrFun h j]
      have := hrows M.1 N.1 M.2 N.2 hne'
      simpa only [ne_eq, Int.cast_inj] using this)
  exact ⟨x, fun M hM => hx ⟨M, hM⟩⟩
