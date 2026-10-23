import AFTD.Prelude
import AFTD.Kb.Tcs.RealApproxDegree
import AFTD.Kb.Tcs.Bit
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.DegreeSpace
import AFTD.Kb.Tcs.HasRealApproximation
import AFTD.Kb.Tcs.G

/-!
# ternary_lift_realApproxDegree_le

Topic: circuits   Node: 84704f6288ba

Provenance: formalization of a published result. Source: arXiv:2610.19174 Theorem 3.2.1, Listing A.9

Suppose n, d : ℕ with 40 ≤ n. If f : (Fin n → Bool) → Bool, P : (Fin n → Bool) → ℝ is in degreeSpace ℝ (Fin n) d, and Z : (Fin n → Bool) → ℤ satisfies -1 ≤ Z x ∧ Z x ≤ 1 for all x, and |P x - (Z x : ℝ) - bit (f x) / 2| ≤ 1 / (20 * (n : ℝ)) for all x, then realApproxDegree f (1 / 3) ≤ 5 * d.
-/

open scoped BigOperators

/-- The monomial `∏_{i ∈ S} x_i` as a function on `{0,1}^n`. -/
def ternary_lift_realApproxDegree_le_kmono {ι : Type*} [DecidableEq ι] (K : Type*) [CommRing K]
    (S : Finset ι) : (ι → Bool) → K :=
  fun x => ∏ i ∈ S, if x i then (1 : K) else 0

lemma ternary_lift_realApproxDegree_le_kmono_apply {ι : Type*} [DecidableEq ι] (K : Type*) [CommRing K]
    (S : Finset ι) (x : ι → Bool) :
    ternary_lift_realApproxDegree_le_kmono K S x = if (∀ i ∈ S, x i = true) then (1 : K) else 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp [ternary_lift_realApproxDegree_le_kmono]
  | insert a S ha ih =>
    simp only [ternary_lift_realApproxDegree_le_kmono] at *
    rw [Finset.prod_insert ha, ih]
    simp only [Finset.forall_mem_insert]
    by_cases hxa : x a = true <;> simp [hxa]

lemma ternary_lift_realApproxDegree_le_kmono_mul {ι : Type*} [DecidableEq ι] (K : Type*) [CommRing K]
    (S T : Finset ι) :
    ternary_lift_realApproxDegree_le_kmono K S * ternary_lift_realApproxDegree_le_kmono K T
      = ternary_lift_realApproxDegree_le_kmono K (S ∪ T) := by
  classical
  funext x
  rw [Pi.mul_apply, ternary_lift_realApproxDegree_le_kmono_apply,
    ternary_lift_realApproxDegree_le_kmono_apply, ternary_lift_realApproxDegree_le_kmono_apply]
  by_cases hS : ∀ i ∈ S, x i = true
  · by_cases hT : ∀ i ∈ T, x i = true
    · have hU : ∀ i ∈ (S ∪ T : Finset ι), x i = true := by
        intro i hi; rcases Finset.mem_union.mp hi with h | h
        · exact hS i h
        · exact hT i h
      rw [if_pos hT, if_pos hS, if_pos hU]; simp
    · have hU : ¬ ∀ i ∈ (S ∪ T : Finset ι), x i = true := by
        intro h; exact hT (fun i hi => h i (Finset.mem_union_right S hi))
      rw [if_neg hT, if_neg hU]; simp
  · by_cases hT : ∀ i ∈ T, x i = true
    · have hU : ¬ ∀ i ∈ (S ∪ T : Finset ι), x i = true := by
        intro h; exact hS (fun i hi => h i (Finset.mem_union_left T hi))
      rw [if_pos hT, if_neg hS, if_neg hU]; simp
    · have hU : ¬ ∀ i ∈ (S ∪ T : Finset ι), x i = true := by
        intro h; exact hS (fun i hi => h i (Finset.mem_union_left T hi))
      rw [if_neg hT, if_neg hS, if_neg hU]; simp

lemma ternary_lift_realApproxDegree_le_degreeSpace_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Type*) [CommRing K] {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    degreeSpace K ι d₁ ≤ degreeSpace K ι d₂ := by
  intro f hf
  rw [degreeSpace] at hf ⊢
  refine Submodule.span_mono ?_ hf
  rintro g ⟨S, hS, rfl⟩
  exact ⟨S, le_trans hS h, rfl⟩

lemma ternary_lift_realApproxDegree_le_degreeSpace_mul_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Type*) [CommRing K] {d₁ d₂ : ℕ} {P Q : (ι → Bool) → K}
    (hP : P ∈ degreeSpace K ι d₁) (hQ : Q ∈ degreeSpace K ι d₂) :
    (fun x => P x * Q x) ∈ degreeSpace K ι (d₁ + d₂) := by
  classical
  have hdeg : ∀ d, degreeSpace K ι d
      = Submodule.span K { f : (ι → Bool) → K | ∃ S : Finset ι, S.card ≤ d ∧
          f = ternary_lift_realApproxDegree_le_kmono K S} := fun d => rfl
  rw [hdeg] at hP hQ ⊢
  have key : (fun x => P x * Q x) ∈
      Submodule.span K { f : (ι → Bool) → K | ∃ S, S.card ≤ d₁ ∧
        f = ternary_lift_realApproxDegree_le_kmono K S} *
      Submodule.span K { f : (ι → Bool) → K | ∃ S, S.card ≤ d₂ ∧
        f = ternary_lift_realApproxDegree_le_kmono K S} := by
    have hmul : P * Q ∈
      Submodule.span K { f : (ι → Bool) → K | ∃ S, S.card ≤ d₁ ∧
        f = ternary_lift_realApproxDegree_le_kmono K S} *
      Submodule.span K { f : (ι → Bool) → K | ∃ S, S.card ≤ d₂ ∧
        f = ternary_lift_realApproxDegree_le_kmono K S} :=
      Submodule.mul_mem_mul hP hQ
    have heq : P * Q = (fun x => P x * Q x) := rfl
    rwa [heq] at hmul
  rw [Submodule.span_mul_span] at key
  refine Submodule.span_mono ?_ key
  rintro f ⟨g, hg, h, hh, rfl⟩
  obtain ⟨S, hS, rfl⟩ := hg
  obtain ⟨T, hT, rfl⟩ := hh
  exact ⟨S ∪ T, by have := Finset.card_union_le S T; omega,
    ternary_lift_realApproxDegree_le_kmono_mul K S T⟩

lemma ternary_lift_realApproxDegree_le_degreeSpace_pow_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Type*) [CommRing K] {d : ℕ} {P : (ι → Bool) → K} (hP : P ∈ degreeSpace K ι d) (k : ℕ) :
    (fun x => P x ^ k) ∈ degreeSpace K ι (k * d) := by
  classical
  induction k with
  | zero =>
    have h0 : (fun x : ι → Bool => P x ^ 0) =
        ternary_lift_realApproxDegree_le_kmono K (∅ : Finset ι) := by
      funext x; simp [ternary_lift_realApproxDegree_le_kmono]
    rw [h0]
    have hmem : ternary_lift_realApproxDegree_le_kmono K (∅ : Finset ι) ∈ degreeSpace K ι 0 := by
      rw [degreeSpace]
      exact Submodule.subset_span ⟨∅, by simp, rfl⟩
    simpa using hmem
  | succ k ih =>
    have he : (fun x : ι → Bool => P x ^ (k + 1)) = (fun x => P x ^ k * P x) := by
      funext x; ring
    rw [he]
    have hm := ternary_lift_realApproxDegree_le_degreeSpace_mul_mem K ih hP
    have hd : k * d + d = (k + 1) * d := by ring
    rwa [hd] at hm

/-- The degree-5 interpolation polynomial used in the ternary lift. -/
noncomputable def ternary_lift_realApproxDegree_le_H (t : ℝ) : ℝ :=
  (2*t^5 - 5*t^4 - 10*t^3 + 20*t^2 + 8*t) / 15

/-- The derivative of the interpolation polynomial. -/
noncomputable def ternary_lift_realApproxDegree_le_H' (t : ℝ) : ℝ :=
  (10*t^4 - 20*t^3 - 30*t^2 + 40*t + 8) / 15

lemma ternary_lift_realApproxDegree_le_H_hasDerivAt (y : ℝ) :
    HasDerivAt ternary_lift_realApproxDegree_le_H (ternary_lift_realApproxDegree_le_H' y) y := by
  have h₁ : HasDerivAt (fun x : ℝ => 2 * x^5) (2 * (5 * y^4)) y := by
    simpa using (hasDerivAt_pow 5 y).const_mul 2
  have h₂ : HasDerivAt (fun x : ℝ => 5 * x^4) (5 * (4 * y^3)) y := by
    simpa using (hasDerivAt_pow 4 y).const_mul 5
  have h₃ : HasDerivAt (fun x : ℝ => 10 * x^3) (10 * (3 * y^2)) y := by
    simpa using (hasDerivAt_pow 3 y).const_mul 10
  have h₄ : HasDerivAt (fun x : ℝ => 20 * x^2) (20 * (2 * y)) y := by
    simpa using (hasDerivAt_pow 2 y).const_mul 20
  have h₅ : HasDerivAt (fun x : ℝ => 8 * x) 8 y := by
    simpa using (hasDerivAt_id y).const_mul 8
  have h := (((h₁.sub h₂).sub h₃).add h₄).add h₅
  have hd := h.div_const 15
  have key : (2 * (5 * y^4) - 5 * (4 * y^3) - 10 * (3 * y^2) + 20 * (2 * y) + 8) / 15
      = ternary_lift_realApproxDegree_le_H' y := by
    unfold ternary_lift_realApproxDegree_le_H'
    ring
  simp only [key] at hd
  unfold ternary_lift_realApproxDegree_le_H
  exact hd

lemma ternary_lift_realApproxDegree_le_H'_abs_le (y : ℝ) (hy1 : -3 ≤ y) (hy2 : y ≤ 4) :
    |ternary_lift_realApproxDegree_le_H' y| ≤ 130 := by
  have hlow : -(1950 : ℝ) ≤ 10*y^4 - 20*y^3 - 30*y^2 + 40*y + 8 := by
    have hfac : 10*y^4 - 20*y^3 - 30*y^2 + 40*y + 8 + 32 = 10*(y^2-y-2)^2 := by ring
    nlinarith [hfac, sq_nonneg (y^2-y-2)]
  have hup : 10*y^4 - 20*y^3 - 30*y^2 + 40*y + 8 ≤ (1950 : ℝ) := by
    have hfac : 10*y^4 - 20*y^3 - 30*y^2 + 40*y + 8 - 968 = 10*(y-4)*(y+3)*(y^2-y+8) := by ring
    have h1 : (y-4) ≤ 0 := by linarith
    have h2 : (0:ℝ) ≤ y+3 := by linarith
    have h3 : (0:ℝ) ≤ y^2-y+8 := by nlinarith [sq_nonneg (2*y-1)]
    have h4 : (y-4)*(y+3) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2
    have h5 : (y-4)*(y+3)*(y^2-y+8) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h4 h3
    nlinarith [hfac]
  have habs : |10*y^4 - 20*y^3 - 30*y^2 + 40*y + 8| ≤ 1950 := by
    rw [abs_le]; exact ⟨hlow, hup⟩
  unfold ternary_lift_realApproxDegree_le_H'
  rw [abs_div, show |(15:ℝ)| = 15 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 15)]
  linarith

lemma ternary_lift_realApproxDegree_le_H_lift (z : ℤ) (b : ℝ) (hz1 : -1 ≤ z) (hz2 : z ≤ 1)
    (hb : b = 0 ∨ b = 1) : ternary_lift_realApproxDegree_le_H (2 * (z:ℝ) + b) = b := by
  have hz : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases hz with h | h | h <;> subst h <;> rcases hb with rfl | rfl <;>
    norm_num [ternary_lift_realApproxDegree_le_H]

lemma ternary_lift_realApproxDegree_le_bit_zero_or_one (b : Bool) : bit b = 0 ∨ bit b = 1 := by
  cases b <;> simp [bit]
lemma ternary_lift_realApproxDegree_le_bit_nonneg (b : Bool) : 0 ≤ bit b := by
  cases b <;> simp [bit]
lemma ternary_lift_realApproxDegree_le_bit_le_one (b : Bool) : bit b ≤ 1 := by
  cases b <;> simp [bit]

/-- Quintic decoder for ternary integer lifts: real 1/3-approximate degree bound. -/
theorem ternary_lift_realApproxDegree_le {n d : ℕ} (hn : 40 ≤ n)
    (f : (Fin n → Bool) → Bool) (P : (Fin n → Bool) → ℝ) (Z : (Fin n → Bool) → ℤ)
    (hP : P ∈ degreeSpace (K := ℝ) (Fin n) d)
    (hZ : ∀ x, -1 ≤ Z x ∧ Z x ≤ 1)
    (happrox : ∀ x, |P x - (Z x : ℝ) - bit (f x) / 2| ≤ 1 / (20 * (n : ℝ))) :
    realApproxDegree f (1 / 3) ≤ 5 * d := by
  have hQ : (fun x => 2 * P x) ∈ degreeSpace (K := ℝ) (Fin n) d := by
    have hEq : (fun x => 2 * P x) = (2:ℝ) • P := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    exact Submodule.smul_mem _ 2 hP
  have hpow := ternary_lift_realApproxDegree_le_degreeSpace_pow_mem (K := ℝ) hQ
  have hmono : ∀ k : ℕ, k ≤ 5 → (fun x => (2*P x)^k) ∈ degreeSpace (K := ℝ) (Fin n) (5*d) := by
    intro k hk
    have hkd : k * d ≤ 5 * d := Nat.mul_le_mul_right d hk
    exact ternary_lift_realApproxDegree_le_degreeSpace_mono ℝ hkd (hpow k)
  have h1 := hmono 1 (by norm_num)
  have h2 := hmono 2 (by norm_num)
  have h3 := hmono 3 (by norm_num)
  have h4 := hmono 4 (by norm_num)
  have h5 := hmono 5 (by norm_num)
  have hcomb : (fun x => ternary_lift_realApproxDegree_le_H (2 * P x)) =
      (2/15 : ℝ) • (fun x => (2*P x)^5) - (1/3 : ℝ) • (fun x => (2*P x)^4)
        - (2/3 : ℝ) • (fun x => (2*P x)^3) + (4/3 : ℝ) • (fun x => (2*P x)^2)
        + (8/15 : ℝ) • (fun x => (2*P x)^1) := by
    funext x
    simp only [ternary_lift_realApproxDegree_le_H, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hmem : (fun x => ternary_lift_realApproxDegree_le_H (2 * P x)) ∈
      degreeSpace (K := ℝ) (Fin n) (5*d) := by
    rw [hcomb]
    have hA := Submodule.smul_mem (degreeSpace (K := ℝ) (Fin n) (5*d)) (2/15:ℝ) h5
    have hB := Submodule.smul_mem (degreeSpace (K := ℝ) (Fin n) (5*d)) (1/3:ℝ) h4
    have hC := Submodule.smul_mem (degreeSpace (K := ℝ) (Fin n) (5*d)) (2/3:ℝ) h3
    have hD := Submodule.smul_mem (degreeSpace (K := ℝ) (Fin n) (5*d)) (4/3:ℝ) h2
    have hE := Submodule.smul_mem (degreeSpace (K := ℝ) (Fin n) (5*d)) (8/15:ℝ) h1
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ hA hB) hC) hD) hE
  have happrox' : ∀ x, |(fun x => ternary_lift_realApproxDegree_le_H (2 * P x)) x - bit (f x)| ≤ 1/3 := by
    intro x
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn40 : (40:ℝ) ≤ n := by exact_mod_cast hn
    have hz1 : (-1:ℝ) ≤ (Z x : ℝ) := by exact_mod_cast (hZ x).1
    have hz2 : (Z x : ℝ) ≤ 1 := by exact_mod_cast (hZ x).2
    have hb0 : 0 ≤ bit (f x) := ternary_lift_realApproxDegree_le_bit_nonneg _
    have hb1 : bit (f x) ≤ 1 := ternary_lift_realApproxDegree_le_bit_le_one _
    have hWlo : -3 ≤ 2 * (Z x : ℝ) + bit (f x) := by linarith
    have hWhi : 2 * (Z x : ℝ) + bit (f x) ≤ 4 := by linarith
    have hd : |2 * P x - (2 * (Z x : ℝ) + bit (f x))| ≤ 1 / (10 * (n:ℝ)) := by
      have hrew : 2 * P x - (2 * (Z x : ℝ) + bit (f x))
          = 2 * (P x - (Z x : ℝ) - bit (f x) / 2) := by ring
      rw [hrew, abs_mul, show |(2:ℝ)| = 2 by norm_num]
      have heq : 2 * (1 / (20 * (n:ℝ))) = 1 / (10 * (n:ℝ)) := by
        field_simp
        ring
      linarith [happrox x]
    have hdle : |2 * P x - (2 * (Z x : ℝ) + bit (f x))| ≤ 1/400 := by
      refine le_trans hd ?_
      have h400 : (400:ℝ) ≤ 10 * n := by linarith
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h400
    have htlo : -3 ≤ 2 * P x := by
      have := (abs_le.mp hdle).1; linarith
    have hthi : 2 * P x ≤ 4 := by
      have := (abs_le.mp hdle).2; linarith
    have hmvt : ‖ternary_lift_realApproxDegree_le_H (2 * P x)
        - ternary_lift_realApproxDegree_le_H (2 * (Z x : ℝ) + bit (f x))‖
        ≤ 130 * ‖2 * P x - (2 * (Z x : ℝ) + bit (f x))‖ := by
      refine Convex.norm_image_sub_le_of_norm_deriv_le
        (f := ternary_lift_realApproxDegree_le_H) (s := Set.Icc (-3:ℝ) 4)
        (x := 2 * (Z x : ℝ) + bit (f x)) (y := 2 * P x) (C := 130) ?_ ?_
        (convex_Icc _ _) ⟨hWlo, hWhi⟩ ⟨htlo, hthi⟩
      · intro y _; exact (ternary_lift_realApproxDegree_le_H_hasDerivAt y).differentiableAt
      · intro y hy
        rw [Real.norm_eq_abs, (ternary_lift_realApproxDegree_le_H_hasDerivAt y).deriv]
        exact ternary_lift_realApproxDegree_le_H'_abs_le y hy.1 hy.2
    have hHW : ternary_lift_realApproxDegree_le_H (2 * (Z x : ℝ) + bit (f x)) = bit (f x) :=
      ternary_lift_realApproxDegree_le_H_lift (Z x) (bit (f x)) (hZ x).1 (hZ x).2
        (ternary_lift_realApproxDegree_le_bit_zero_or_one _)
    calc |ternary_lift_realApproxDegree_le_H (2 * P x) - bit (f x)|
        = ‖ternary_lift_realApproxDegree_le_H (2 * P x)
            - ternary_lift_realApproxDegree_le_H (2 * (Z x : ℝ) + bit (f x))‖ := by
          rw [hHW, Real.norm_eq_abs]
      _ ≤ 130 * ‖2 * P x - (2 * (Z x : ℝ) + bit (f x))‖ := hmvt
      _ = 130 * |2 * P x - (2 * (Z x : ℝ) + bit (f x))| := by rw [Real.norm_eq_abs]
      _ ≤ 130 * (1 / (10 * (n:ℝ))) := by gcongr
      _ = 13 / (n:ℝ) := by field_simp; ring
      _ ≤ 13 / 40 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn40
      _ ≤ 1/3 := by norm_num
  have hhas : HasRealApproximation f (5 * d) (1 / 3) :=
    ⟨fun x => ternary_lift_realApproxDegree_le_H (2 * P x), hmem, happrox'⟩
  unfold realApproxDegree
  exact Nat.sInf_le hhas
