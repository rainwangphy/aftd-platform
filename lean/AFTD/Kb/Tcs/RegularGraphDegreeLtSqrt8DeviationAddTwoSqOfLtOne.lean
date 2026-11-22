import AFTD.Prelude
import AFTD.Kb.Tcs.RegularGraphMooreCubicEqOnesDegreeLeTwo
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# regular_graph_degree_lt_sqrt8_deviation_add_two_sq_of_lt_one

Topic: graphs   Node: 3b0a29022e65

Provenance: formalization of a published result. Source: arXiv:2611.26037 (An improved Moore bound for girths seven and eleven), proof of Theorem 3.1, Theorem 3.1 in the case r < 1 (first step of its proof).

Let H be a finite nonempty d-regular simple graph with adjacency matrix A, and let C = A^3 + A^2 - 2(d-1)A - (d-1)I - J. If every row of C has absolute row sum at most r and r < 1, then d < (√8 r + 2)^2. (This is the case r < 1 of the deviation bound: the integer row sums vanish, so H is a Moore graph of diameter 3 and d ≤ 2.)
-/

theorem regular_graph_degree_lt_sqrt8_deviation_add_two_sq_of_lt_one (d : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hne : Nonempty W) (hreg : H.IsRegularOfDegree d) (r : ℝ)
    (hr : ∀ u : W, ((∑ v : W, |((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) - Matrix.of (fun _ _ => (1 : ℤ)) : Matrix W W ℤ) u v| : ℤ) : ℝ) ≤ r)
    (hr1 : r < 1) :
    (d : ℝ) < (Real.sqrt 8 * r + 2) ^ 2 := by
  obtain ⟨u0⟩ := hne
  have hr0 : 0 ≤ r := by
    refine le_trans ?_ (hr u0)
    exact_mod_cast Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hzero : ∀ u v, ((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ
      - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) - Matrix.of (fun _ _ => (1 : ℤ)) : Matrix W W ℤ) u v = 0 := by
    intro u v
    have h1 : ((∑ v : W, |((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ
        - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) - Matrix.of (fun _ _ => (1 : ℤ)) : Matrix W W ℤ) u v| : ℤ) : ℝ) < 1 :=
      lt_of_le_of_lt (hr u) hr1
    have h2 : (∑ v : W, |((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ
        - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) - Matrix.of (fun _ _ => (1 : ℤ)) : Matrix W W ℤ) u v| : ℤ) = 0 := by
      have h3 : (∑ v : W, |((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ
        - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) - Matrix.of (fun _ _ => (1 : ℤ)) : Matrix W W ℤ) u v| : ℤ) < 1 := by
        exact_mod_cast h1
      have h4 := Finset.sum_nonneg (fun v (_ : v ∈ Finset.univ) => abs_nonneg ((((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ
        - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) - Matrix.of (fun _ _ => (1 : ℤ)) : Matrix W W ℤ) u v)))
      omega
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => abs_nonneg _)).mp h2 v (Finset.mem_univ v)
    exact abs_eq_zero.mp h5
  have hC : ((H.adjMatrix ℤ) ^ 3 + (H.adjMatrix ℤ) ^ 2 - (2 * ((d : ℤ) - 1)) • H.adjMatrix ℤ
        - ((d : ℤ) - 1) • (1 : Matrix W W ℤ) : Matrix W W ℤ) = Matrix.of (fun _ _ => (1 : ℤ)) := by
    ext u v
    have := hzero u v
    rw [Matrix.sub_apply] at this
    linarith
  have hd := regular_graph_moore_cubic_eq_ones_degree_le_two d W H ⟨u0⟩ hreg hC
  have hdR : (d : ℝ) ≤ 2 := by exact_mod_cast hd
  have hs : 0 ≤ Real.sqrt 8 * r := mul_nonneg (Real.sqrt_nonneg 8) hr0
  nlinarith
