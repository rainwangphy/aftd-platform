import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanAvoidsAp
import AFTD.Kb.Tcs.EuclideanHasMonoAp

/-!
# op_1481_avoidance_three_twenty_one_dim_one

Topic: combinatorics   Node: 8bb52f2a2855

Provenance: formalization of a published result. Source: arXiv:2611.12360 (Avoiding short progressions in Euclidean Ramsey theory II), Sec. 3.3

For every real number $\alpha > 0$ such that $\alpha^2 \in \{1/4, 1/9, 2/15, 3/4\}$, euclidean_avoids_ap 1 3 1 21 α holds: there exists a two-coloring of 1-dimensional Euclidean space containing neither a monochromatic 3-term arithmetic progression with unit spacing of color false nor a monochromatic 21-term arithmetic progression with spacing $\alpha$ of color true.
-/

open scoped RealInnerProductSpace in
lemma op_1481_avoidance_three_twenty_one_dim_one_norm_eq_abs_coord
    (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma op_1481_avoidance_three_twenty_one_dim_one_decide_even (a b : ℤ)
    (h : decide (Even a) = decide (Even b)) : Even a ↔ Even b := by
  by_cases ha : Even a <;> by_cases hb : Even b <;> simp [ha, hb] at h ⊢

lemma op_1481_avoidance_three_twenty_one_dim_one_floor_add_mem (y d : ℝ) (h : |d| < 1) :
    ⌊y + d⌋ = ⌊y⌋ - 1 ∨ ⌊y + d⌋ = ⌊y⌋ ∨ ⌊y + d⌋ = ⌊y⌋ + 1 := by
  have hd1 : -1 < d := by linarith [neg_abs_le d]
  have hd2 : d < 1 := by linarith [le_abs_self d]
  have hle : ⌊d⌋ ≤ 0 := by
    have : ⌊d⌋ < (1:ℤ) := by rw [Int.floor_lt]; simpa using hd2
    omega
  have hge : -1 ≤ ⌊d⌋ := by
    rw [Int.le_floor]; push_cast; linarith
  have h1 : ⌊y⌋ + ⌊d⌋ ≤ ⌊y + d⌋ := Int.le_floor_add y d
  have h2 : ⌊y + d⌋ - 1 ≤ ⌊y⌋ + ⌊d⌋ := Int.le_floor_add_floor y d
  omega

lemma op_1481_avoidance_three_twenty_one_dim_one_floor_parity_ne_of_abs_one
    (x d : ℝ) (hd : |d| = 1) : ¬ (Even ⌊x + d⌋ ↔ Even ⌊x⌋) := by
  have hd' : d = 1 ∨ d = -1 := (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hd
  rcases hd' with rfl | hd'
  · rw [Int.floor_add_one, Int.even_add_one]
    tauto
  · rw [hd']
    rw [show x + -1 = x - 1 by ring, Int.floor_sub_one]
    rw [show Even (⌊x⌋ - 1) ↔ ¬ Even ⌊x⌋ by
      rw [Int.even_sub]; simp]
    tauto

lemma op_1481_avoidance_three_twenty_one_dim_one_floor_parity_not_const
    (x d : ℝ) (hlt : |d| < 1) (hbig : 1 < 20 * |d|) :
    ¬ (∀ k : Fin 21, Even ⌊x + (k : ℝ) * d⌋ ↔ Even ⌊x⌋) := by
  intro H
  set a : ℕ → ℤ := fun k => ⌊x + (k : ℝ) * d⌋ with ha
  have H' : ∀ k : ℕ, k ≤ 20 → (Even (a k) ↔ Even (a 0)) := by
    intro k hk
    have hk21 : k < 21 := by omega
    have := H ⟨k, hk21⟩
    simpa [a] using this
  have hstep : ∀ m : ℕ, m < 20 → a (m+1) = a m := by
    intro m hm
    have heq : a (m+1) = ⌊x + (m : ℝ) * d + d⌋ := by
      simp only [a]
      congr 1
      push_cast
      ring
    have hdisj : a (m+1) = a m - 1 ∨ a (m+1) = a m ∨ a (m+1) = a m + 1 := by
      have h := op_1481_avoidance_three_twenty_one_dim_one_floor_add_mem
        (x + (m : ℝ) * d) d hlt
      rw [heq]
      simpa [a] using h
    have hp : Even (a (m+1)) ↔ Even (a m) := (H' (m+1) (by omega)).trans (H' m (by omega)).symm
    have hev : Even (a (m+1) - a m) := Int.even_sub.mpr hp
    rcases hdisj with h | h | h
    · rw [h] at hev; norm_num at hev
    · exact h
    · rw [h] at hev; norm_num at hev
  have hconst : a 20 = a 0 := by
    suffices hall : ∀ k, k ≤ 20 → a k = a 0 by exact hall 20 (le_refl 20)
    intro k hk
    induction k with
    | zero => rfl
    | succ m ih =>
      have hm : m < 20 := by omega
      calc a (m+1) = a m := hstep m hm
        _ = a 0 := ih (by omega)
  by_cases hd : 0 ≤ d
  · have hD : (1:ℝ) < 20 * d := by
      rw [abs_of_nonneg hd] at hbig; exact hbig
    have hreal : (a 20 : ℝ) > (a 0 : ℝ) := by
      have h1 : (a 20 : ℝ) > x + 20 * d - 1 := by
        have hlt' := Int.lt_floor_add_one (x + (20:ℝ)*d)
        have hcast : (a 20 : ℝ) = (⌊x + (20:ℝ)*d⌋ : ℝ) := by simp [a]
        rw [hcast]; linarith
      have h2 : x + 20 * d - 1 > x := by linarith
      have h3 : (a 0 : ℝ) ≤ x := by
        have := Int.floor_le x
        simpa [a] using this
      linarith
    rw [hconst] at hreal; linarith
  · have hdneg : d < 0 := by linarith
    have hD : 20 * d < -1 := by
      have habs : |d| = -d := abs_of_neg hdneg
      rw [habs] at hbig; linarith
    have hreal : (a 20 : ℝ) < (a 0 : ℝ) := by
      have h1 : (a 20 : ℝ) ≤ x + (20:ℝ)*d := by
        have := Int.floor_le (x + (20:ℝ)*d)
        have hcast : (a 20 : ℝ) = (⌊x + (20:ℝ)*d⌋ : ℝ) := by simp [a]
        rw [hcast]; exact this
      have h2 : x + 20 * d < x - 1 := by linarith
      have h3 : x - 1 < (a 0 : ℝ) := by
        have := Int.sub_one_lt_floor x
        simpa [a] using this
      linarith
    rw [hconst] at hreal; linarith

lemma op_1481_avoidance_three_twenty_one_dim_one_aux (α : ℝ)
    (h1 : (1:ℝ)/20 < α) (h2 : α < 1) : euclidean_avoids_ap 1 3 1 21 α := by
  refine ⟨fun x => decide (Even ⌊x 0⌋), ?_, ?_⟩
  · rintro ⟨x₀, v, hv, h⟩
    have hcoord : |v 0| = 1 := by
      have hnorm := op_1481_avoidance_three_twenty_one_dim_one_norm_eq_abs_coord v
      rw [hv] at hnorm
      exact hnorm.symm
    have hpar := op_1481_avoidance_three_twenty_one_dim_one_floor_parity_ne_of_abs_one
      (x₀ 0) (v 0) hcoord
    apply hpar
    have h0 : decide (Even ⌊x₀ 0⌋) = false := by simpa using h 0
    have h1' : decide (Even ⌊(x₀ + (1:ℝ) • v) 0⌋) = false := by
      have hk := h 1
      simpa using hk
    have heq : decide (Even ⌊x₀ 0 + v 0⌋) = decide (Even ⌊x₀ 0⌋) := by
      have hcoord1 : (x₀ + (1:ℝ) • v) 0 = x₀ 0 + v 0 := by simp
      rw [← hcoord1, h1', h0]
    exact op_1481_avoidance_three_twenty_one_dim_one_decide_even _ _ heq
  · rintro ⟨x₀, v, hv, h⟩
    have hcoord : |v 0| = α := by
      have hnorm := op_1481_avoidance_three_twenty_one_dim_one_norm_eq_abs_coord v
      rw [hv] at hnorm
      exact hnorm.symm
    have hlt : |v 0| < 1 := by rw [hcoord]; exact h2
    have hbig : 1 < 20 * |v 0| := by rw [hcoord]; linarith
    apply op_1481_avoidance_three_twenty_one_dim_one_floor_parity_not_const
      (x₀ 0) (v 0) hlt hbig
    intro k
    have hk : decide (Even ⌊(x₀ + (k:ℝ) • v) 0⌋) = true := h k
    have h0 : decide (Even ⌊x₀ 0⌋) = true := by simpa using h 0
    have heq : decide (Even ⌊(x₀ + (k:ℝ) • v) 0⌋) = decide (Even ⌊x₀ 0⌋) := hk.trans h0.symm
    have hcoordk : (x₀ + (k:ℝ) • v) 0 = x₀ 0 + (k:ℝ) * v 0 := by simp
    rw [← hcoordk]
    exact op_1481_avoidance_three_twenty_one_dim_one_decide_even _ _ heq

/-- Avoidance of 21-term arithmetic progressions at the exceptional squared spacings in dimension 1. -/
theorem op_1481_avoidance_three_twenty_one_dim_one
    (α : ℝ) (hα : 0 < α) (h_sq : α ^ 2 ∈ ({1 / 4, 1 / 9, 2 / 15, 3 / 4} : Set ℝ)) :
    euclidean_avoids_ap 1 3 1 21 α := by
  have hmem : α ^ 2 = 1/4 ∨ α ^ 2 = 1/9 ∨ α ^ 2 = 2/15 ∨ α ^ 2 = 3/4 := by
    simpa using h_sq
  have h1 : (1:ℝ)/20 < α := by rcases hmem with h | h | h | h <;> nlinarith
  have h2 : α < 1 := by rcases hmem with h | h | h | h <;> nlinarith
  exact op_1481_avoidance_three_twenty_one_dim_one_aux α h1 h2
