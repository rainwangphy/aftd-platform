import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCutCount

/-!
# digraph_min_cut_eq_half_sum_sub_half_abs_diff

Topic: graphs   Node: 8bc823a2331b

Provenance: helper lemma. arXiv:2610.21381 Section 5 line 1572

For any two vertex subsets A and B in a finite digraph G, the minimum of the directed cut counts e(A, B) and e(B, A) in ℚ equals half their sum minus half the absolute value of their difference.
-/

/-- For any vertex subsets A and B in a digraph, min(e(A, B), e(B, A)) = (e(A, B) + e(B, A))/2 - |e(A, B) - e(B, A)|/2. -/
theorem digraph_min_cut_eq_half_sum_sub_half_abs_diff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (min (digraph_cut_count G A B : ℚ) (digraph_cut_count G B A : ℚ)) =
      ((digraph_cut_count G A B : ℚ) + (digraph_cut_count G B A : ℚ)) / 2 -
      |(digraph_cut_count G A B : ℚ) - (digraph_cut_count G B A : ℚ)| / 2 := by
  rcases le_total (digraph_cut_count G A B : ℚ) (digraph_cut_count G B A : ℚ) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring
