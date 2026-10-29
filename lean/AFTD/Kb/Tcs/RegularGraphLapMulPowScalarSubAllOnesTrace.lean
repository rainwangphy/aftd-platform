import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLapTraceSeq

/-!
# regular_graph_lap_mul_pow_scalar_sub_all_ones_trace

Topic: graphs   Node: 05d9ed686ec0

Provenance: formalization of a published result. Source: arXiv:2610.36127 Lemma 34

For each d-regular graph G on n vertices and each pair of positive integers i and j, the trace of L(G)^i ((d+1)I_n - J_n)^j equals (d+1)^j ℓ_i(G), where J_n is the all-ones matrix and ℓ_i(G) is the Laplacian trace sequence.
-/

/-- If `L * J = 0` (`J` the all-ones matrix), then `L * ((d+1)I - J)^j = (d+1)^j • L`. -/
lemma regular_graph_lap_mul_pow_scalar_sub_all_ones_trace_aux1 {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (d : ℕ)
    (hLJ : L * Matrix.of (fun (_ _ : V) ↦ (1 : ℝ)) = 0) (j : ℕ) :
    L * (((d + 1 : ℝ) • (1 : Matrix V V ℝ) - Matrix.of fun (_ _ : V) ↦ (1 : ℝ)) ^ j) =
      ((d + 1 : ℝ) ^ j) • L := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hLA : L * ((d + 1 : ℝ) • (1 : Matrix V V ℝ) - Matrix.of fun (_ _ : V) ↦ (1 : ℝ)) =
        (d + 1 : ℝ) • L := by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hLJ, sub_zero]
    rw [pow_succ, ← mul_assoc, ih, Matrix.smul_mul, hLA, smul_smul, pow_succ]

/-- Hence `L^(m+1) * ((d+1)I - J)^j = (d+1)^j • L^(m+1)`. -/
lemma regular_graph_lap_mul_pow_scalar_sub_all_ones_trace_aux2 {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (d : ℕ)
    (hLJ : L * Matrix.of (fun (_ _ : V) ↦ (1 : ℝ)) = 0) (m j : ℕ) :
    L ^ (m + 1) * (((d + 1 : ℝ) • (1 : Matrix V V ℝ) - Matrix.of fun (_ _ : V) ↦ (1 : ℝ)) ^ j) =
      ((d + 1 : ℝ) ^ j) • L ^ (m + 1) := by
  rw [pow_succ, mul_assoc, regular_graph_lap_mul_pow_scalar_sub_all_ones_trace_aux1 L d hLJ j,
    Matrix.mul_smul, ← pow_succ]

/-- Taking traces: `tr (L^i ((d+1)I - J)^j) = (d+1)^j tr (L^i)` for positive `i`, `j`. -/
lemma regular_graph_lap_mul_pow_scalar_sub_all_ones_trace_aux3 {V : Type*} [Fintype V] [DecidableEq V]
    (L : Matrix V V ℝ) (d : ℕ)
    (hLJ : L * Matrix.of (fun (_ _ : V) ↦ (1 : ℝ)) = 0) (i j : ℕ+) :
    (L ^ (i : ℕ) * (((d + 1 : ℝ) • (1 : Matrix V V ℝ) - Matrix.of fun (_ _ : V) ↦ (1 : ℝ)) ^ (j : ℕ))).trace =
      ((d + 1 : ℝ) ^ (j : ℕ)) * (L ^ (i : ℕ)).trace := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show (i : ℕ) ≠ 0 from i.pos.ne')
  rw [hm, regular_graph_lap_mul_pow_scalar_sub_all_ones_trace_aux2 L d hLJ m (j : ℕ),
    Matrix.trace_smul, smul_eq_mul]

open scoped Classical in
/-- For any d-regular graph G and positive integers i and j, the trace of L(G)^i ((d+1)I - J)^j equals (d+1)^j tr(L(G)^i). -/
theorem regular_graph_lap_mul_pow_scalar_sub_all_ones_trace
    {V : Type*} [Fintype V] (d : ℕ) (G : SimpleGraph V)
    (hreg : G.IsRegularOfDegree d) (i j : ℕ+) :
    Matrix.trace (((G.lapMatrix ℝ) ^ (i : ℕ)) *
      (((d + 1 : ℝ) • (1 : Matrix V V ℝ) - Matrix.of fun (_ _ : V) ↦ (1 : ℝ)) ^ (j : ℕ))) =
    ((d + 1 : ℝ) ^ (j : ℕ)) * graph_lap_trace_seq G i := by
  classical
  have hLJ : G.lapMatrix ℝ * Matrix.of (fun (_ _ : V) ↦ (1 : ℝ)) = 0 := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, mul_one, Matrix.zero_apply]
    have h := congrFun (SimpleGraph.lapMatrix_mulVec_const_eq_zero (G := G) (R := ℝ)) a
    simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply, Pi.zero_apply, mul_one] at h
    simpa using h
  exact regular_graph_lap_mul_pow_scalar_sub_all_ones_trace_aux3 (G.lapMatrix ℝ) d hLJ i j
