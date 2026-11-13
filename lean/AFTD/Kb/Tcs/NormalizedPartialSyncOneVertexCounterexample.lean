import AFTD.Prelude
import AFTD.Kb.Tcs.NormalizedOrderedPartialMixture

/-!
# normalized_partial_sync_one_vertex_counterexample

Topic: combinatorics   Node: 6db9347352cd

Provenance: helper lemma. A synthetic obstruction to an abstract closure argument for OP-1399.

Even with the normalized sequence invariant, the natural one-vertex extension can fail the partial-synchronization inequality at indices five and four.
-/

private noncomputable def normalized_partial_sync_one_vertex_counterexample_u (k : ℕ) : ℝ :=
  if k = 0 then 1
  else if k = 1 then 1
  else if k = 2 then 998001 / 1000000
  else if k = 3 then 181904741342743902183 / 5000000000000000000000
  else if k = 4 then 66200407293111997854969150264421196067 / 50000000000000000000000000000000000000000
  else if k = 5 then 481272732631301529159448892272789453226703549914335353280180491 / 10000000000000000000000000000000000000000000000000000000000000000000
  else if k = 6 then 8733878705367771705347830564266662493759325047014297649576423308008142692692608463914730009 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  else 0

private noncomputable def normalized_partial_sync_one_vertex_counterexample_a (k : ℕ) : ℝ :=
  if k = 0 then 1
  else if k = 1 then 1
  else if k = 2 then 280438281 / 10000000000
  else if k = 3 then 786265849191860254791 / 1000000000000000000000000
  else if k = 4 then 200577353440324411411324440353395564203 / 10000000000000000000000000000000000000000000
  else if k = 5 then 412659512093234101377042736551617840750391434855265139981580421 / 1000000000000000000000000000000000000000000000000000000000000000000000
  else if k = 6 then 8733878705367771705347830564266662493759325047014297649576423308008142692692608463914730009 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  else 0

private theorem normalized_partial_sync_one_vertex_counterexample_u_zero (k : ℕ) (h : 6 < k) :
    normalized_partial_sync_one_vertex_counterexample_u k = 0 := by
  unfold normalized_partial_sync_one_vertex_counterexample_u; split_ifs <;> (try rfl) <;> omega

private theorem normalized_partial_sync_one_vertex_counterexample_a_zero (k : ℕ) (h : 6 < k) :
    normalized_partial_sync_one_vertex_counterexample_a k = 0 := by
  unfold normalized_partial_sync_one_vertex_counterexample_a; split_ifs <;> (try rfl) <;> omega

private theorem normalized_partial_sync_one_vertex_counterexample_valid :
    normalized_ordered_partial_mixture normalized_partial_sync_one_vertex_counterexample_u normalized_partial_sync_one_vertex_counterexample_a := by
  refine ⟨by unfold normalized_partial_sync_one_vertex_counterexample_a; norm_num,
          by unfold normalized_partial_sync_one_vertex_counterexample_u; norm_num,
          by unfold normalized_partial_sync_one_vertex_counterexample_a; norm_num,
          by unfold normalized_partial_sync_one_vertex_counterexample_u; norm_num,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k ≤ 6
    · interval_cases k <;> (unfold normalized_partial_sync_one_vertex_counterexample_a normalized_partial_sync_one_vertex_counterexample_u; norm_num)
    · have h : 6 < k := by omega
      simp [normalized_partial_sync_one_vertex_counterexample_a_zero k h, normalized_partial_sync_one_vertex_counterexample_u_zero k h]
  · intro k hk
    simp [normalized_partial_sync_one_vertex_counterexample_a_zero k hk, normalized_partial_sync_one_vertex_counterexample_u_zero k hk]
  · intro i j hij
    by_cases hj : j ≤ 6
    · have hi : i ≤ 5 := by omega
      interval_cases j <;> interval_cases i <;> (unfold normalized_partial_sync_one_vertex_counterexample_a normalized_partial_sync_one_vertex_counterexample_u; norm_num)
    · have hj' : 6 < j := by omega
      simp [normalized_partial_sync_one_vertex_counterexample_a_zero j hj', normalized_partial_sync_one_vertex_counterexample_u_zero j hj']
  · intro k
    by_cases hk : k ≤ 4
    · interval_cases k <;> (unfold normalized_partial_sync_one_vertex_counterexample_a normalized_partial_sync_one_vertex_counterexample_u; norm_num)
    · have h : 6 < k + 2 := by omega
      simp only [normalized_partial_sync_one_vertex_counterexample_a_zero (k+2) h, normalized_partial_sync_one_vertex_counterexample_u_zero (k+2) h, sub_self, mul_zero]
      exact sq_nonneg _
  · intro t ht0 ht1 k
    by_cases hk : k ≤ 4
    · have h1 : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
      have h3 : 0 ≤ t ^ 2 := sq_nonneg _
      interval_cases k <;> (unfold normalized_partial_sync_one_vertex_counterexample_a normalized_partial_sync_one_vertex_counterexample_u; norm_num; nlinarith)
    · have h : 6 < k + 2 := by omega
      simp only [normalized_partial_sync_one_vertex_counterexample_a_zero (k+2) h, normalized_partial_sync_one_vertex_counterexample_u_zero (k+2) h, sub_self, mul_zero, add_zero]
      exact sq_nonneg _
  · intro i j hj hji
    by_cases hi : i ≤ 6
    · have hj6 : j ≤ 6 := by omega
      have hi1 : 1 ≤ i := by omega
      interval_cases i <;> interval_cases j <;> (unfold normalized_partial_sync_one_vertex_counterexample_a normalized_partial_sync_one_vertex_counterexample_u; norm_num)
    · have h0 : 6 < i := by omega
      have h1 : 6 < i + 1 := by omega
      simp [normalized_partial_sync_one_vertex_counterexample_a_zero i h0, normalized_partial_sync_one_vertex_counterexample_u_zero i h0, normalized_partial_sync_one_vertex_counterexample_a_zero (i+1) h1, normalized_partial_sync_one_vertex_counterexample_u_zero (i+1) h1]

theorem normalized_partial_sync_one_vertex_counterexample : ∃ u a : ℕ → ℝ, normalized_ordered_partial_mixture u a ∧ (let g : ℕ → ℝ := fun k => (20 - (k : ℝ)) * u k + (k : ℝ) * a (k - 1); let q : ℕ → ℝ := fun k => (20 - (k : ℝ)) * u k + (k : ℝ) * u (k - 1); g 5 * q 4 + g 4 * q 5 < g 6 * q 3 + g 3 * q 6) := by
  refine ⟨normalized_partial_sync_one_vertex_counterexample_u, normalized_partial_sync_one_vertex_counterexample_a,
          normalized_partial_sync_one_vertex_counterexample_valid, ?_⟩
  unfold normalized_partial_sync_one_vertex_counterexample_u normalized_partial_sync_one_vertex_counterexample_a
  norm_num
