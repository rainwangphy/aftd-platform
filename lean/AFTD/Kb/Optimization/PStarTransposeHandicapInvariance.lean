import AFTD.Prelude
import AFTD.Kb.Optimization.IsPStar
import AFTD.Kb.Optimization.HandicapNumber
import AFTD.Kb.Optimization.IsPStarKappa

/-!
# p_star_transpose_handicap_invariance

Topic: lp_duality   Node: 94089eef9a33

Provenance: formalization of a published result. Source: arXiv:2611.07815 Theorem 2.6

For every natural number n and every real n-by-n matrix M indexed by Fin n in the class P*, its transpose M.transpose belongs to the class P*, and their handicap numbers coincide: handicap_number n M.transpose = handicap_number n M.
-/

/-- A lower bound `c ‖u‖² ≤ ‖B u‖²` (c > 0) passes from a square matrix to its transpose. -/
theorem pstar_tr_sigma_min {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (h : ∀ u : Fin n → ℝ, c * dotProduct u u ≤ dotProduct (Matrix.mulVec B u) (Matrix.mulVec B u)) :
    ∀ v : Fin n → ℝ, c * dotProduct v v ≤
      dotProduct (Matrix.mulVec B.transpose v) (Matrix.mulVec B.transpose v) := by
  have hinj : Function.Injective (Matrix.mulVec B) := by
    intro a b hab
    have h0 := h (a - b)
    rw [Matrix.mulVec_sub, hab, sub_self, dotProduct_zero] at h0
    have h1 : 0 ≤ dotProduct (a - b) (a - b) := by
      unfold dotProduct; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have h2 : dotProduct (a - b) (a - b) = 0 := by nlinarith
    rw [dotProduct_self_eq_zero] at h2
    exact sub_eq_zero.mp h2
  have hsurj : Function.Surjective (Matrix.mulVec B) :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  intro v
  obtain ⟨u, rfl⟩ := hsurj v
  set w := Matrix.mulVec B.transpose (Matrix.mulVec B u) with hw
  have hdual : dotProduct w u = dotProduct (Matrix.mulVec B u) (Matrix.mulVec B u) := by
    rw [hw, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  have hcs : (dotProduct w u) ^ 2 ≤ dotProduct w w * dotProduct u u := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w u
    simpa [dotProduct, sq] using this
  set a := dotProduct (Matrix.mulVec B u) (Matrix.mulVec B u)
  set b := dotProduct w w
  set s := dotProduct u u
  have ha : 0 ≤ a := by
    simp only [a, dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hb : 0 ≤ b := by
    simp only [b, dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hs : 0 ≤ s := by
    simp only [s, dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hcsa : c * s ≤ a := h u
  rw [hdual] at hcs
  rcases ha.lt_or_eq with ha' | ha'
  · have : c * a * a ≤ b * a := by nlinarith
    nlinarith
  · rw [← ha']; simpa using hb

/-- The scaled matrix `1 + α D⁻¹ M D⁻¹` applied to a vector. -/
theorem pstar_tr_B_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) (α : ℝ)
    (u : Fin n → ℝ) (i : Fin n) :
    Matrix.mulVec (1 + α • (Matrix.diagonal (fun j => (e j)⁻¹) * M * Matrix.diagonal (fun j => (e j)⁻¹))) u i
      = u i + α * ((e i)⁻¹ * Matrix.mulVec M (fun j => (e j)⁻¹ * u j) i) := by
  have hd : ∀ v : Fin n → ℝ, (Matrix.diagonal fun j => (e j)⁻¹).mulVec v = fun j => (e j)⁻¹ * v j := by
    intro v; funext j; simp [Matrix.mulVec_diagonal]
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hd]

theorem pstar_tr_B_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) (α : ℝ) :
    (1 + α • (Matrix.diagonal (fun j => (e j)⁻¹) * M * Matrix.diagonal (fun j => (e j)⁻¹))).transpose
      = 1 + α • (Matrix.diagonal (fun j => (e j)⁻¹) * M.transpose * Matrix.diagonal (fun j => (e j)⁻¹)) := by
  simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The norm identity behind the scaling: `‖B u‖² - (1-α²)‖u‖² = 2α W(x)` with `x = D⁻¹ u`. -/
theorem pstar_tr_identity {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) (he : ∀ i, 0 < e i)
    (α : ℝ) (u : Fin n → ℝ) :
    dotProduct (Matrix.mulVec (1 + α • (Matrix.diagonal (fun j => (e j)⁻¹) * M * Matrix.diagonal (fun j => (e j)⁻¹))) u)
      (Matrix.mulVec (1 + α • (Matrix.diagonal (fun j => (e j)⁻¹) * M * Matrix.diagonal (fun j => (e j)⁻¹))) u)
      - (1 - α ^ 2) * dotProduct u u
      = 2 * α * ∑ i, ((fun j => (e j)⁻¹ * u j) i * Matrix.mulVec M (fun j => (e j)⁻¹ * u j) i
          + α / 2 * ((e i) ^ 2 * ((fun j => (e j)⁻¹ * u j) i) ^ 2
            + (Matrix.mulVec M (fun j => (e j)⁻¹ * u j) i) ^ 2 / (e i) ^ 2)) := by
  simp only [dotProduct, pstar_tr_B_mulVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hei : e i ≠ 0 := (he i).ne'
  field_simp
  ring

/-- Diagonally weighted form `W_e(N, x)`. -/
theorem pstar_tr_weighted {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) (he : ∀ i, 0 < e i)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hW : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (x i * Matrix.mulVec M x i
      + α / 2 * ((e i) ^ 2 * (x i) ^ 2 + (Matrix.mulVec M x i) ^ 2 / (e i) ^ 2))) :
    ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (x i * Matrix.mulVec M.transpose x i
      + α / 2 * ((e i) ^ 2 * (x i) ^ 2 + (Matrix.mulVec M.transpose x i) ^ 2 / (e i) ^ 2)) := by
  have hc : 0 < 1 - α ^ 2 := by nlinarith
  have hB := pstar_tr_sigma_min
    (1 + α • (Matrix.diagonal (fun j => (e j)⁻¹) * M * Matrix.diagonal (fun j => (e j)⁻¹)))
    (1 - α ^ 2) hc (fun u => by
      have h1 := pstar_tr_identity M e he α u
      have h2 := hW (fun j => (e j)⁻¹ * u j)
      nlinarith)
  rw [pstar_tr_B_transpose] at hB
  intro x
  have h1 := pstar_tr_identity M.transpose e he α (fun j => e j * x j)
  have hx : (fun j => (e j)⁻¹ * (e j * x j)) = x := by
    funext j; field_simp [(he j).ne']
  rw [hx] at h1
  have h2 := hB (fun j => e j * x j)
  by_contra hneg
  push Not at hneg
  nlinarith

/-- AM-GM: the plain condition gives every weighted one. -/
theorem pstar_tr_amgm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hS : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (x i * Matrix.mulVec M x i + α * |x i * Matrix.mulVec M x i|))
    (e : Fin n → ℝ) (he : ∀ i, 0 < e i) :
    ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (x i * Matrix.mulVec M x i
      + α / 2 * ((e i) ^ 2 * (x i) ^ 2 + (Matrix.mulVec M x i) ^ 2 / (e i) ^ 2)) := by
  intro x
  refine le_trans (hS x) (Finset.sum_le_sum (fun i _ => ?_))
  have hei : e i ≠ 0 := (he i).ne'
  set p := x i
  set q := Matrix.mulVec M x i
  have key : 2 * |p * q| ≤ (e i) ^ 2 * p ^ 2 + q ^ 2 / (e i) ^ 2 := by
    have h := two_mul_le_add_sq (e i * |p|) (|q| / e i)
    have hab : e i * |p| * (|q| / e i) = |p * q| := by rw [abs_mul]; field_simp
    have ha : (e i * |p|) ^ 2 = (e i) ^ 2 * p ^ 2 := by rw [mul_pow, sq_abs]
    have hb : (|q| / e i) ^ 2 = q ^ 2 / (e i) ^ 2 := by rw [div_pow, sq_abs]
    rw [mul_assoc, hab, ha, hb] at h
    exact h
  nlinarith

/-- Taking the weights to the limit recovers the plain condition. -/
theorem pstar_tr_limit {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hW : ∀ e : Fin n → ℝ, (∀ i, 0 < e i) → ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (x i * Matrix.mulVec N x i
      + α / 2 * ((e i) ^ 2 * (x i) ^ 2 + (Matrix.mulVec N x i) ^ 2 / (e i) ^ 2))) :
    ∀ x : Fin n → ℝ, 0 ≤ ∑ i, (x i * Matrix.mulVec N x i + α * |x i * Matrix.mulVec N x i|) := by
  intro x
  set G := ∑ i, (x i * Matrix.mulVec N x i + α * |x i * Matrix.mulVec N x i|)
  set C := α / 2 * ∑ i, (|x i| + |Matrix.mulVec N x i|)
  have hC : 0 ≤ C := by
    apply mul_nonneg (by linarith)
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have ht : ∀ t : ℝ, 0 < t → 0 ≤ G + t * C := by
    intro t ht
    have h := hW (fun i => Real.sqrt ((|Matrix.mulVec N x i| + t) / (|x i| + t)))
      (fun i => Real.sqrt_pos.mpr (by positivity)) x
    refine le_trans h ?_
    simp only [G, C, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    set p := x i
    set q := Matrix.mulVec N x i
    have hd : (Real.sqrt ((|q| + t) / (|p| + t))) ^ 2 = (|q| + t) / (|p| + t) :=
      Real.sq_sqrt (by positivity)
    rw [hd]
    have hp : 0 < |p| + t := by positivity
    have hq : 0 < |q| + t := by positivity
    have h1 : (|q| + t) / (|p| + t) * p ^ 2 ≤ |p| * (|q| + t) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hp, ← sq_abs p]
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg p) hq.le) ht.le]
    have h2 : q ^ 2 / ((|q| + t) / (|p| + t)) ≤ |q| * (|p| + t) := by
      rw [div_div_eq_mul_div, div_le_iff₀ hq, ← sq_abs q]
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg q) hp.le) ht.le]
    have h3 : (|q| + t) / (|p| + t) * p ^ 2 + q ^ 2 / ((|q| + t) / (|p| + t))
        ≤ 2 * |p * q| + t * (|p| + |q|) := by
      rw [abs_mul]; nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ α / 2 by linarith)
    nlinarith
  by_contra hneg
  push Not at hneg
  have h := ht (-G / (2 * (C + 1))) (div_pos (by linarith) (by linarith))
  have hle : -G / (2 * (C + 1)) * C ≤ -G / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  linarith

/-- The P*(κ) condition in the form `Σ (p + α|p|) ≥ 0`, `α = 2κ/(1+2κ)`. -/
theorem pstar_tr_kappa_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ) :
    is_p_star_kappa n M κ ↔ 0 ≤ κ ∧ ∀ x : Fin n → ℝ,
      0 ≤ ∑ i, (x i * Matrix.mulVec M x i + 2 * κ / (1 + 2 * κ) * |x i * Matrix.mulVec M x i|) := by
  unfold is_p_star_kappa
  constructor
  · rintro ⟨hκ, h⟩
    refine ⟨hκ, fun x => ?_⟩
    have hx := h x
    have hk : 0 < 1 + 2 * κ := by linarith
    have heq : (1 + 4 * κ) * (∑ i ∈ Finset.univ.filter (fun i => 0 < x i * (Matrix.mulVec M x) i), x i * (Matrix.mulVec M x) i) +
      (∑ i ∈ Finset.univ.filter (fun i => x i * (Matrix.mulVec M x) i < 0), x i * (Matrix.mulVec M x) i)
      = (1 + 2 * κ) * ∑ i, (x i * Matrix.mulVec M x i + 2 * κ / (1 + 2 * κ) * |x i * Matrix.mulVec M x i|) := by
      rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      set p := x i * Matrix.mulVec M x i
      rcases lt_trichotomy p 0 with hp | hp | hp
      · rw [if_neg (by linarith), if_pos hp, abs_of_neg hp]; field_simp; ring
      · rw [hp]; simp
      · rw [if_pos hp, if_neg (by linarith), abs_of_pos hp]; field_simp; ring
    rw [heq] at hx
    exact (mul_nonneg_iff_of_pos_left hk).mp hx
  · rintro ⟨hκ, h⟩
    refine ⟨hκ, fun x => ?_⟩
    have hx := h x
    have hk : 0 < 1 + 2 * κ := by linarith
    have heq : (1 + 4 * κ) * (∑ i ∈ Finset.univ.filter (fun i => 0 < x i * (Matrix.mulVec M x) i), x i * (Matrix.mulVec M x) i) +
      (∑ i ∈ Finset.univ.filter (fun i => x i * (Matrix.mulVec M x) i < 0), x i * (Matrix.mulVec M x) i)
      = (1 + 2 * κ) * ∑ i, (x i * Matrix.mulVec M x i + 2 * κ / (1 + 2 * κ) * |x i * Matrix.mulVec M x i|) := by
      rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      set p := x i * Matrix.mulVec M x i
      rcases lt_trichotomy p 0 with hp | hp | hp
      · rw [if_neg (by linarith), if_pos hp, abs_of_neg hp]; field_simp; ring
      · rw [hp]; simp
      · rw [if_pos hp, if_neg (by linarith), abs_of_pos hp]; field_simp; ring
    rw [heq]
    exact mul_nonneg hk.le hx

theorem pstar_tr_kappa_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ)
    (h : is_p_star_kappa n M κ) : is_p_star_kappa n M.transpose κ := by
  rw [pstar_tr_kappa_iff] at h ⊢
  obtain ⟨hκ, hS⟩ := h
  refine ⟨hκ, ?_⟩
  have hk : 0 < 1 + 2 * κ := by linarith
  rcases hκ.lt_or_eq with hκ' | hκ'
  · have hα0 : 0 < 2 * κ / (1 + 2 * κ) := by positivity
    have hα1 : 2 * κ / (1 + 2 * κ) < 1 := by rw [div_lt_one hk]; linarith
    exact pstar_tr_limit M.transpose _ hα0.le (fun e he =>
      pstar_tr_weighted M e he _ hα0 hα1 (pstar_tr_amgm M _ hα0.le hS e he))
  · subst hκ'
    intro x
    have hx := hS x
    have hsym : ∑ i, x i * Matrix.mulVec M.transpose x i = ∑ i, x i * Matrix.mulVec M x i := by
      have : dotProduct x (Matrix.mulVec M.transpose x) = dotProduct x (Matrix.mulVec M x) := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
      simpa [dotProduct] using this
    simp only [mul_zero, zero_div, zero_mul, add_zero] at hx ⊢
    rw [hsym]; exact hx

/-- Transposition invariance of the class P* and the handicap number. -/
theorem p_star_transpose_handicap_invariance (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : is_p_star n M) :
    is_p_star n M.transpose ∧ handicap_number n M.transpose = handicap_number n M := by
  have hset : {κ : ℝ | is_p_star_kappa n M.transpose κ} = {κ : ℝ | is_p_star_kappa n M κ} := by
    ext κ
    constructor
    · intro h
      have := pstar_tr_kappa_transpose M.transpose κ h
      simpa using this
    · exact pstar_tr_kappa_transpose M κ
  refine ⟨?_, ?_⟩
  · obtain ⟨κ, hκ, h⟩ := hM
    exact ⟨κ, hκ, pstar_tr_kappa_transpose M κ h⟩
  · unfold handicap_number
    rw [hset]
