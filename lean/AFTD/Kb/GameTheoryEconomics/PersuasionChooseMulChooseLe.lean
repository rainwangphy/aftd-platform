import AFTD.Prelude

/-!
# persuasion_choose_mul_choose_le

Topic: mechanism_design   Node: 570cbcde8fd5

Lemma A. If d, N ≥ 1 and d + N = 2k + 1, then C(d,t) C(N,k-t) ≤ C(2k,k).
-/

open Finset in
/-- `C(N, r) ≤ C(N, r+1)` when `2r+1 ≤ N`. -/
lemma persuasion_choose_le_succ {N r : ℕ} (h : 2 * r + 1 ≤ N) :
    N.choose r ≤ N.choose (r + 1) := by
  have e := Nat.choose_succ_right_eq N r
  have h2 : r + 1 ≤ N - r := by omega
  have : N.choose r * (r + 1) ≤ N.choose (r + 1) * (r + 1) := by
    rw [e]; exact Nat.mul_le_mul_left _ h2
  exact Nat.le_of_mul_le_mul_right this (Nat.succ_pos r)

open Finset in
/-- Two distinct antidiagonal terms of Vandermonde's sum are at most the total. -/
lemma persuasion_two_terms_le (a b k i j : ℕ) (hij : i < j) (hj : j ≤ k) :
    a.choose i * b.choose (k - i) + a.choose j * b.choose (k - j) ≤ (a + b).choose k := by
  rw [Nat.add_choose_eq]
  have hsub : ({(i, k - i), (j, k - j)} : Finset (ℕ × ℕ)) ⊆ antidiagonal k := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [Finset.HasAntidiagonal.mem_antidiagonal] <;> omega
  have hne : (i, k - i) ≠ (j, k - j) := by
    intro h; simp at h; omega
  calc a.choose i * b.choose (k - i) + a.choose j * b.choose (k - j)
      = ∑ p ∈ ({(i, k - i), (j, k - j)} : Finset (ℕ × ℕ)), a.choose p.1 * b.choose p.2 := by
        rw [sum_pair hne]
    _ ≤ ∑ p ∈ antidiagonal k, a.choose p.1 * b.choose p.2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

open Finset in
/-- **Lemma A.** If `d, N ≥ 1` and `d + N = 2k + 1`, then `C(d,t) C(N,k-t) ≤ C(2k,k)`. -/
lemma persuasion_choose_mul_choose_le (d N k t : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hs : d + N = 2 * k + 1) (ht : t ≤ k) :
    d.choose t * N.choose (k - t) ≤ (2 * k).choose k := by
  rcases Nat.lt_or_ge (2 * t) d with h | h
  · -- `2t + 1 ≤ d`: split the second factor, use `C(d,t) ≤ C(d,t+1)`.
    have htk : t < k := by
      by_contra h'; omega
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    obtain ⟨r, hr⟩ : ∃ r, k - t = r + 1 := ⟨k - t - 1, by omega⟩
    have hpas : (N' + 1).choose (r + 1) = N'.choose r + N'.choose (r + 1) :=
      Nat.choose_succ_succ N' r
    have hmono : d.choose t ≤ d.choose (t + 1) := persuasion_choose_le_succ (by omega)
    have hv := persuasion_two_terms_le d N' k t (t + 1) (by omega) (by omega)
    have e1 : k - t = r + 1 := hr
    have e2 : k - (t + 1) = r := by omega
    rw [e2, e1] at hv
    have hdk : d + N' = 2 * k := by omega
    rw [hdk] at hv
    rw [hr, hpas, Nat.mul_add]
    calc d.choose t * N'.choose r + d.choose t * N'.choose (r + 1)
        ≤ d.choose (t + 1) * N'.choose r + d.choose t * N'.choose (r + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ hmono) _
      _ = d.choose t * N'.choose (r + 1) + d.choose (t + 1) * N'.choose r := by ring
      _ ≤ (2 * k).choose k := hv
  · -- `d ≤ 2t`: split the first factor, use `C(N,k-t) ≤ C(N,k-t+1)`.
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hpas : (d' + 1).choose (t' + 1) = d'.choose t' + d'.choose (t' + 1) :=
      Nat.choose_succ_succ d' t'
    have hmono : N.choose (k - (t' + 1)) ≤ N.choose (k - (t' + 1) + 1) :=
      persuasion_choose_le_succ (by omega)
    have e3 : k - (t' + 1) + 1 = k - t' := by omega
    rw [e3] at hmono
    have hv := persuasion_two_terms_le d' N k t' (t' + 1) (by omega) (by omega)
    have hdk : d' + N = 2 * k := by omega
    rw [hdk] at hv
    rw [hpas, Nat.add_mul]
    calc d'.choose t' * N.choose (k - (t' + 1)) + d'.choose (t' + 1) * N.choose (k - (t' + 1))
        ≤ d'.choose t' * N.choose (k - t') + d'.choose (t' + 1) * N.choose (k - (t' + 1)) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hmono) _
      _ ≤ (2 * k).choose k := hv
