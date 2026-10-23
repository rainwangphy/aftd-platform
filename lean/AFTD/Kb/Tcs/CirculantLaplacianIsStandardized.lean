import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# circulant_laplacian_is_standardized

Topic: graphs   Node: d40209410872

Provenance: helper lemma. arXiv:2610.14100 proof of Corollary 2

For n ≥ 2 and coefficients t_m ∈ [0, 1] for m = 1, ..., n-1, the matrix (1/n) ∑_{m=1}^{n-1} t_m (I - Q^m), where Q is the cyclic permutation matrix, is a standardized Laplacian matrix of order n.
-/

lemma circulant_laplacian_is_standardized_indicator_one (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, (if i = j then (1:ℝ) else 0)) = 1 := by
  rw [Finset.sum_ite_eq]; simp

lemma circulant_laplacian_is_standardized_indicator_mod (n r : ℕ) (hr : r < n) :
    (∑ j : Fin n, (if j.val = r then (1:ℝ) else 0)) = 1 := by
  have h : ∀ j : Fin n, (if j.val = r then (1:ℝ) else 0) = (if j = ⟨r, hr⟩ then 1 else 0) := by
    intro j; simp [Fin.ext_iff]
  simp only [h]
  rw [Finset.sum_ite_eq']; simp

lemma circulant_laplacian_is_standardized_indicator_le_one (n : ℕ) (i j : Fin n) :
    (∑ m ∈ Finset.Ico 1 n, (if j.val = (i.val + m) % n then (1:ℝ) else 0)) ≤ 1 := by
  rw [Finset.sum_boole]
  have hcard : ((Finset.Ico 1 n).filter (fun m => j.val = (i.val + m) % n)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
    obtain ⟨⟨ha1, ha2⟩, hpa⟩ := ha
    obtain ⟨⟨hb1, hb2⟩, hpb⟩ := hb
    have hmod : (i.val + a) ≡ (i.val + b) [MOD n] := by
      unfold Nat.ModEq; rw [← hpa, ← hpb]
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' i.val hmod) ha2 hb2
  exact_mod_cast hcard

/-- The circulant Laplacian matrix formed from cyclic permutation matrices is a standardized Laplacian matrix. -/
theorem circulant_laplacian_is_standardized (n : ℕ) (hn : 2 ≤ n) (t : ℕ → ℝ)
    (ht : ∀ m ∈ Finset.Ico 1 n, 0 ≤ t m ∧ t m ≤ 1) :
    is_standardized_laplacian n
      ((1 / (n : ℝ)) • ∑ m ∈ Finset.Ico 1 n, (t m) •
        ((1 : Matrix (Fin n) (Fin n) ℝ) - (Matrix.of fun (i j : Fin n) => if j.val = (i.val + m) % n then 1 else 0))) := by
  let M : Matrix (Fin n) (Fin n) ℝ :=
    (1 / (n : ℝ)) • ∑ m ∈ Finset.Ico 1 n, (t m) •
      ((1 : Matrix (Fin n) (Fin n) ℝ) - (Matrix.of (fun (i j : Fin n) => (if j.val = (i.val + m) % n then (1:ℝ) else 0) : Fin n → Fin n → ℝ)))
  change is_standardized_laplacian n M
  unfold is_standardized_laplacian
  have hM : ∀ (i j : Fin n), M i j = (1/(n:ℝ)) * ∑ m ∈ Finset.Ico 1 n, t m * (((1 : Matrix (Fin n) (Fin n) ℝ) i j) - ((Matrix.of (fun (i j : Fin n) => (if j.val = (i.val + m) % n then (1:ℝ) else 0) : Fin n → Fin n → ℝ)) i j)) := by
    intro i j
    simp only [M, Matrix.smul_apply, Matrix.sum_apply, Matrix.sub_apply, smul_eq_mul]
  constructor
  · intro i
    simp only [hM]
    rw [← Finset.mul_sum]
    have hzero : (∑ j : Fin n, ∑ m ∈ Finset.Ico 1 n, t m *
        ((1 : Matrix (Fin n) (Fin n) ℝ) i j - Matrix.of (fun (i j : Fin n) => (if j.val = (i.val + m) % n then (1:ℝ) else 0) : Fin n → Fin n → ℝ) i j)) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro m hm
      rw [← Finset.mul_sum]
      have hrow : (∑ j : Fin n, ((1 : Matrix (Fin n) (Fin n) ℝ) i j - Matrix.of (fun (i j : Fin n) => (if j.val = (i.val + m) % n then (1:ℝ) else 0) : Fin n → Fin n → ℝ) i j)) = 0 := by
        rw [Finset.sum_sub_distrib]
        simp only [Matrix.one_apply, Matrix.of_apply]
        rw [circulant_laplacian_is_standardized_indicator_one n i,
            circulant_laplacian_is_standardized_indicator_mod n ((i.val + m) % n) (Nat.mod_lt _ (by omega))]
        ring
      rw [hrow, mul_zero]
    rw [hzero, mul_zero]
  · intro i j hij
    simp only [hM]
    simp only [Matrix.one_apply, Matrix.of_apply, if_neg hij]
    set S := ∑ m ∈ Finset.Ico 1 n, t m * (if j.val = (i.val + m) % n then (1:ℝ) else 0) with hS
    have hsum : (∑ m ∈ Finset.Ico 1 n, t m * (0 - (if j.val = (i.val + m) % n then (1:ℝ) else 0))) = -S := by
      rw [hS, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    rw [hsum]
    have hS_nonneg : 0 ≤ S := by
      rw [hS]
      apply Finset.sum_nonneg
      intro m hm
      have h1 := (ht m hm).1
      have hind : (0:ℝ) ≤ (if j.val = (i.val + m) % n then (1:ℝ) else 0) := by split <;> norm_num
      exact mul_nonneg h1 hind
    have hS_le : S ≤ 1 := by
      rw [hS]
      calc ∑ m ∈ Finset.Ico 1 n, t m * (if j.val = (i.val + m) % n then (1:ℝ) else 0)
          ≤ ∑ m ∈ Finset.Ico 1 n, 1 * (if j.val = (i.val + m) % n then (1:ℝ) else 0) := by
            apply Finset.sum_le_sum
            intro m hm
            have ht1 := (ht m hm).2
            have hind : (0:ℝ) ≤ (if j.val = (i.val + m) % n then (1:ℝ) else 0) := by split <;> norm_num
            exact mul_le_mul_of_nonneg_right ht1 hind
        _ = ∑ m ∈ Finset.Ico 1 n, (if j.val = (i.val + m) % n then (1:ℝ) else 0) := by
            apply Finset.sum_congr rfl; intro m hm; ring
        _ ≤ 1 := circulant_laplacian_is_standardized_indicator_le_one n i j
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h1n : (0:ℝ) < 1/(n:ℝ) := by positivity
    constructor
    · rw [show (1:ℝ)/↑n * -S = -((1:ℝ)/↑n * S) by ring, show (-1:ℝ)/↑n = -((1:ℝ)/↑n) by ring]
      rw [neg_le_neg_iff]
      simpa using mul_le_mul_of_nonneg_left hS_le (le_of_lt h1n)
    · rw [show (1:ℝ)/↑n * -S = -((1:ℝ)/↑n * S) by ring]
      rw [neg_nonpos]
      exact mul_nonneg (le_of_lt h1n) hS_nonneg
