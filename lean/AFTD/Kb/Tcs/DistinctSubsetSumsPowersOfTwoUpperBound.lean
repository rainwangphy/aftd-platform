import AFTD.Prelude
import AFTD.Kb.Tcs.DistinctSubsetSumsAdmissible
import AFTD.Kb.Tcs.VectorSeqMaxEntry

/-!
# distinct_subset_sums_powers_of_two_upper_bound

Topic: combinatorics   Node: 3be20e90b4dd

Provenance: formalization of a published result. Source: arXiv:2610.26970 line 140

For all integers k ≥ 1 and n ≥ 1, there exists an admissible sequence a : Fin n → Fin k → ℕ whose maximum entry is at most 2^(Nat.ceil (n / k) - 1).
-/

/-- Powers-of-two upper bound: there exists an admissible sequence with maximum entry at most 2^(ceil(n/k) - 1). -/
theorem distinct_subset_sums_powers_of_two_upper_bound (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∃ (a : Fin n → Fin k → ℕ),
      distinct_subset_sums_admissible a ∧
      vector_seq_max_entry a ≤ 2 ^ (Nat.ceil ((n : ℝ) / (k : ℝ)) - 1) := by
  let a : Fin n → Fin k → ℕ := fun i j => if i.1 % k = j.1 then 2 ^ (i.1 / k) else 0
  use a
  constructor
  · intro S T hST
    ext x
    have hj_lt : x.1 % k < k := Nat.mod_lt x.1 (by omega)
    let j : Fin k := ⟨x.1 % k, hj_lt⟩
    have hj : x.1 % k = j.1 := rfl
    have h_sum (U : Finset (Fin n)) :
        ∑ m ∈ (U.filter (fun i => i.1 % k = j.1)).image (fun i => i.1 / k), 2 ^ m =
        (∑ i ∈ U, a i j) := by
      dsimp [a]
      rw [← Finset.sum_filter]
      have hinj : Set.InjOn (fun (i : Fin n) => i.1 / k) ↑(U.filter (fun i => i.1 % k = j.1)) := by
        intro p hp q hq (hpq : p.1 / k = q.1 / k)
        simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
        have hp_mod : p.1 % k = j.1 := hp.2
        have hq_mod : q.1 % k = j.1 := hq.2
        ext
        calc p.1
          _ = k * (p.1 / k) + p.1 % k := (Nat.div_add_mod p.1 k).symm
          _ = k * (q.1 / k) + q.1 % k := by rw [hpq, hp_mod, hq_mod]
          _ = q.1 := Nat.div_add_mod q.1 k
      exact Finset.sum_image hinj
    have hST_j : (∑ i ∈ S, a i j) = (∑ i ∈ T, a i j) := by
      have h := congr_fun hST j
      rw [Finset.sum_apply, Finset.sum_apply] at h
      exact h
    have h_img_sum :
        ∑ m ∈ (S.filter (fun i => i.1 % k = j.1)).image (fun i => i.1 / k), 2 ^ m =
        ∑ m ∈ (T.filter (fun i => i.1 % k = j.1)).image (fun i => i.1 / k), 2 ^ m := by
      rw [h_sum S, h_sum T, hST_j]
    have h_img_eq := Finset.geomSum_injective (by decide) h_img_sum
    constructor
    · intro hxS
      have hx_filt : x ∈ S.filter (fun i => i.1 % k = j.1) := by
        rw [Finset.mem_filter]
        exact ⟨hxS, hj⟩
      have hx_img : x.1 / k ∈ (S.filter (fun i => i.1 % k = j.1)).image (fun i => i.1 / k) :=
        Finset.mem_image_of_mem _ hx_filt
      rw [h_img_eq] at hx_img
      rcases Finset.mem_image.mp hx_img with ⟨y, hy, hy_div⟩
      rw [Finset.mem_filter] at hy
      have hy_mod : y.1 % k = j.1 := hy.2
      have hxy : x = y := by
        ext
        calc x.1
          _ = k * (x.1 / k) + x.1 % k := (Nat.div_add_mod x.1 k).symm
          _ = k * (y.1 / k) + y.1 % k := by rw [← hy_div, hj, hy_mod]
          _ = y.1 := Nat.div_add_mod y.1 k
      rw [hxy]
      exact hy.1
    · intro hxT
      have hx_filt : x ∈ T.filter (fun i => i.1 % k = j.1) := by
        rw [Finset.mem_filter]
        exact ⟨hxT, hj⟩
      have hx_img : x.1 / k ∈ (T.filter (fun i => i.1 % k = j.1)).image (fun i => i.1 / k) :=
        Finset.mem_image_of_mem _ hx_filt
      rw [← h_img_eq] at hx_img
      rcases Finset.mem_image.mp hx_img with ⟨y, hy, hy_div⟩
      rw [Finset.mem_filter] at hy
      have hy_mod : y.1 % k = j.1 := hy.2
      have hxy : x = y := by
        ext
        calc x.1
          _ = k * (x.1 / k) + x.1 % k := (Nat.div_add_mod x.1 k).symm
          _ = k * (y.1 / k) + y.1 % k := by rw [← hy_div, hj, hy_mod]
          _ = y.1 := Nat.div_add_mod y.1 k
      rw [hxy]
      exact hy.1
  · have h_bound : (n - 1) / k ≤ Nat.ceil ((n : ℝ) / (k : ℝ)) - 1 := by
      have hk0 : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
      have hmul : (n - 1) / k * k ≤ n - 1 := Nat.div_mul_le_self (n - 1) k
      have hlt : n - 1 < n := Nat.sub_lt hn (by decide)
      have hlt2 : (n - 1) / k * k < n := lt_of_le_of_lt hmul hlt
      have h_lt : (((n - 1) / k : ℕ) : ℝ) < (n : ℝ) / (k : ℝ) := by
        rw [lt_div_iff₀ hk0]
        calc (((n - 1) / k : ℕ) : ℝ) * (k : ℝ)
          _ = (((n - 1) / k * k : ℕ) : ℝ) := by push_cast; rfl
          _ < (n : ℝ) := Nat.cast_lt.mpr hlt2
      have hceil : (n - 1) / k < Nat.ceil ((n : ℝ) / (k : ℝ)) := Nat.lt_ceil.mpr h_lt
      exact Nat.le_sub_one_of_lt hceil
    unfold vector_seq_max_entry
    rw [Finset.sup_le_iff]
    rintro ⟨i, j⟩ -
    dsimp [a]
    split_ifs with h
    · have hi : i.1 ≤ n - 1 := Nat.le_pred_of_lt i.isLt
      have hdiv : i.1 / k ≤ (n - 1) / k := Nat.div_le_div_right hi
      have hle : i.1 / k ≤ Nat.ceil ((n : ℝ) / (k : ℝ)) - 1 := le_trans hdiv h_bound
      exact Nat.pow_le_pow_right (by decide) hle
    · exact Nat.zero_le _
