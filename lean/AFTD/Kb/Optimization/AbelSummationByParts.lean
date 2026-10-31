import AFTD.Prelude
import AFTD.Kb.Tcs.Weight

/-!
# abel_summation_by_parts

Topic: submodular   Node: 934a63d8cea2

Provenance: helper lemma. arXiv:2610.35433 Corollary 1 proof

For any positive dimension n, vector a, permutation π of Fin n, and vector z summing to 1, the inner product ∑ i, a i * z i equals a(π(0)) plus the sum over k from 0 to n-2 of (a(π(k+1)) - a(π(k))) times the sum of z over the upper set of elements with rank at least k+1.
-/

/-- Abel summation by parts in range form: the weighted sum equals the first weight times the
total mass plus a telescoping sum against suffix sums. -/
private lemma abel_summation_by_parts_range_identity (N : ℕ) (b w : ℕ → ℝ) (hN : 0 < N) :
    ∑ i ∈ Finset.range N, b i * w i =
      b 0 * (∑ i ∈ Finset.range N, w i) +
        ∑ k ∈ Finset.range (N - 1),
          (b (k + 1) - b k) * ∑ j ∈ (Finset.range N).filter (fun j => k + 1 ≤ j), w j := by
  have hmain := Finset.sum_range_by_parts b w N
  simp only [smul_eq_mul] at hmain
  rw [hmain]
  have hS : ∀ k ∈ Finset.range (N - 1),
      (∑ j ∈ (Finset.range N).filter (fun j => k + 1 ≤ j), w j)
        = (∑ j ∈ Finset.range N, w j) - ∑ j ∈ Finset.range (k + 1), w j := by
    intro k hk
    have hk' : k + 1 ≤ N := by
      have : k < N - 1 := Finset.mem_range.mp hk
      omega
    exact (Finset.sum_range_sub_sum_range (f := w) hk').symm
  have hS2 : (∑ k ∈ Finset.range (N - 1), (b (k + 1) - b k) * ∑ j ∈ (Finset.range N).filter (fun j => k + 1 ≤ j), w j)
      = ∑ k ∈ Finset.range (N - 1), (b (k + 1) - b k) * ((∑ j ∈ Finset.range N, w j) - ∑ j ∈ Finset.range (k + 1), w j) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hS k hk]
  rw [hS2]
  have h1 : (∑ k ∈ Finset.range (N - 1), (b (k + 1) - b k) * ((∑ j ∈ Finset.range N, w j) - ∑ j ∈ Finset.range (k + 1), w j))
      = (∑ k ∈ Finset.range (N - 1), (b (k + 1) - b k) * (∑ j ∈ Finset.range N, w j)) - ∑ k ∈ Finset.range (N - 1), (b (k + 1) - b k) * ∑ j ∈ Finset.range (k + 1), w j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [h1]
  have h2 : (∑ k ∈ Finset.range (N - 1), (b (k + 1) - b k) * (∑ j ∈ Finset.range N, w j))
      = (∑ k ∈ Finset.range (N - 1), (b (k + 1) - b k)) * (∑ j ∈ Finset.range N, w j) := by
    rw [Finset.sum_mul]
  rw [h2, Finset.sum_range_sub]
  ring

/-- A suffix sum over `Fin n` agrees with the corresponding suffix sum over `range n` after
extending the function by zero off the range. -/
private lemma abel_summation_by_parts_inner_sum_range {n : ℕ} (w : Fin n → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => m + 1 ≤ (j : ℕ)), w j)
    = ∑ j ∈ (Finset.range n).filter (fun j => m + 1 ≤ j), (fun k => if h : k < n then w ⟨k, h⟩ else 0) j := by
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if m + 1 ≤ k then (if h : k < n then w ⟨k, h⟩ else 0) else 0) n]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : m + 1 ≤ (j : ℕ)
  · rw [if_pos h]
    rw [dif_pos j.isLt]
    simp [h]
  · rw [if_neg h]
    simp [h]

/-- The Abel summation identity expressed over `Fin n`: the weighted sum equals the first weight
plus a telescoping sum weighted by suffix sums. -/
private lemma abel_summation_by_parts_fin_identity {n : ℕ} (hn : 0 < n) (b w : Fin n → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, b i * w i = b ⟨0, hn⟩ + ∑ k : Fin (n - 1),
      (b ⟨k.val + 1, by omega⟩ - b ⟨k.val, by omega⟩) *
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => k.val + 1 ≤ (j : ℕ)), w j := by
  set B : ℕ → ℝ := fun m => if h : m < n then b ⟨m, h⟩ else 0
  set W : ℕ → ℝ := fun m => if h : m < n then w ⟨m, h⟩ else 0
  have hB : ∀ i : Fin n, B i.val = b i := by intro i; simp [B, i.isLt]
  have hW : ∀ i : Fin n, W i.val = w i := by intro i; simp [W, i.isLt]
  have hWsum : ∑ m ∈ Finset.range n, W m = 1 := by
    rw [← Fin.sum_univ_eq_sum_range W n]
    rw [show (∑ i : Fin n, W ↑i) = ∑ i : Fin n, w i from Finset.sum_congr rfl (fun i _ => hW i)]
    exact hw
  have hr := abel_summation_by_parts_range_identity n B W hn
  rw [hWsum] at hr
  have hB0 : B 0 = b ⟨0, hn⟩ := by simp [B, hn]
  rw [hB0, mul_one] at hr
  have hLHS : ∑ i : Fin n, b i * w i = ∑ i ∈ Finset.range n, B i * W i := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => B m * W m) n]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hB i, hW i]
  have hRHS : (∑ k : Fin (n - 1),
      (b ⟨k.val + 1, by omega⟩ - b ⟨k.val, by omega⟩) *
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => k.val + 1 ≤ (j : ℕ)), w j)
    = ∑ k ∈ Finset.range (n - 1),
        (B (k + 1) - B k) * ∑ j ∈ (Finset.range n).filter (fun j => k + 1 ≤ j), W j := by
    refine Finset.sum_bij (fun (k : Fin (n - 1)) _ => k.val) ?_ ?_ ?_ ?_
    · intro k hk; exact Finset.mem_range.mpr k.isLt
    · intro k1 _ k2 _ heq; exact Fin.ext heq
    · intro m hm
      exact ⟨⟨m, Finset.mem_range.mp hm⟩, Finset.mem_univ _, rfl⟩
    · intro k hk
      rw [hB ⟨k.val, by omega⟩, hB ⟨k.val + 1, by omega⟩]
      congr 1
      exact abel_summation_by_parts_inner_sum_range w k.val
  rw [hLHS, hRHS]
  rw [hr]

/-- Summation by parts (Abel summation) for an observable expectation over a probability distribution. -/
theorem abel_summation_by_parts {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (z : Fin n → ℝ) (hz_sum : ∑ i, z i = 1) :
    ∑ i, a i * z i =
      a (π ⟨0, hn⟩) + ∑ k : Fin (n - 1),
        (a (π ⟨k.val + 1, by omega⟩) - a (π ⟨k.val, by omega⟩)) *
          ∑ i ∈ (Finset.univ.filter (fun j : Fin n => k.val + 1 ≤ (j : ℕ))).map π.toEmbedding, z i := by
  have hw : ∑ i : Fin n, z (π i) = 1 := by
    rw [Equiv.sum_comp π z, hz_sum]
  have hmain := abel_summation_by_parts_fin_identity hn (fun i => a (π i)) (fun i => z (π i)) hw
  rw [← Equiv.sum_comp π (fun i => a i * z i)]
  rw [hmain]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [Finset.sum_map]
  rfl
