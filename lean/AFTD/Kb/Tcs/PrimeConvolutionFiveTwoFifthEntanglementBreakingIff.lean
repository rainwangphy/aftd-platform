import AFTD.Prelude
import AFTD.Kb.Tcs.PrimeConvolutionChoi
import AFTD.Kb.Tcs.TwoLevelEnvironment
import AFTD.Kb.Tcs.MatrixIsSeparable
import AFTD.Kb.Tcs.PrimeConvolutionSeparableImpThreshold

/-!
# prime_convolution_five_two_fifth_entanglement_breaking_iff

Topic: quantum   Node: bd35becd0457

Provenance: original. Related work: OP-2466 (proposed here; it builds on the qutrit convolution channels of arXiv:2609.16200, whose Theorem 8 gives the exact PPT and entanglement-breaking threshold 2/5 on a balanced two-level qutrit slice, and on arXiv:2611.09594, which shows PPT and entanglement breaking differ for another convolution environment). Smallest instance of the entry: d = 5, r = 2, p = 1/5, threshold 1/3; the product-orbit decomposition of experiment 41963, twirled, is checked exactly in experiment 42119.

For every real t with 0 ≤ t ≤ 1: the matrix prime_convolution_choi 5 2 (two_level_environment 5 (1/5) t) (d = 5, r = 2, p = 1/5) is separable if and only if t ≤ 1/3.
-/

open Fin.CommRing in
theorem in1243b_cast (n : ℕ) (a : Fin (n+2)) : (((a : ℕ) : ZMod (n+2))) = a :=
  ZMod.natCast_zmod_val (n := n+2) a

open Fin.CommRing in
theorem in1243b_entry (n : ℕ) (r : Fin (n+2)) (σ : Matrix (Fin (n+2)) (Fin (n+2)) ℂ)
    (x y : Fin (n+2) × Fin (n+2)) :
    prime_convolution_choi (n+2) r σ x y = (1 / ((n+2 : ℕ) : ℂ)) * ∑ j : Fin (n+2), ∑ l : Fin (n+2),
      if x.2 = r * x.1 + j ∧ y.2 = r * y.1 + l ∧ x.1 + j = y.1 + l then σ j l else 0 := by
  simp only [prime_convolution_choi, Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have e : ∀ a : Fin (n+2), (((a : ℕ) : ZMod (n+2))) = a := in1243b_cast n
  erw [e x.1, e x.2, e y.1, e y.2, e j, e l]
  rfl


open Fin.CommRing in
theorem in1243_chi_add (n : ℕ) (u v : Fin (n+2)) :
    (ZMod.stdAddChar (N := n+2) ((u + v : Fin (n+2)))) = ZMod.stdAddChar (N := n+2) u * ZMod.stdAddChar (N := n+2) v :=
  AddChar.map_add_eq_mul _ u v

open Fin.CommRing in
theorem in1243_chi_star (n : ℕ) (u : Fin (n+2)) :
    star (ZMod.stdAddChar (N := n+2) u) = ZMod.stdAddChar (N := n+2) ((-u : Fin (n+2))) := by
  exact (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := n+2)) (u : ZMod (n+2))).symm

open Fin.CommRing in
theorem in1243_chi_sum (n : ℕ) (m : Fin (n+2)) :
    ∑ c : Fin (n+2), ZMod.stdAddChar (N := n+2) ((c * m : Fin (n+2))) = if m = 0 then ((n+2 : ℕ) : ℂ) else 0 := by
  have := AddChar.sum_mulShift (R := ZMod (n+2)) (ψ := ZMod.stdAddChar (N := n+2)) (m : ZMod (n+2))
    (ZMod.isPrimitive_stdAddChar (n+2))
  rw [ZMod.card] at this
  refine Eq.trans this ?_
  by_cases h : m = 0
  · rw [if_pos h]
    exact congrArg Nat.cast (if_pos (show (m : ZMod (n+2)) = 0 from h))
  · rw [if_neg h]
    exact (congrArg Nat.cast (if_neg (show ¬ (m : ZMod (n+2)) = 0 from h))).trans Nat.cast_zero

theorem in1243_sep_add (dA dB : ℕ) (A B : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hA : matrix_is_separable dA dB A) (hB : matrix_is_separable dA dB B) :
    matrix_is_separable dA dB (A + B) := by
  obtain ⟨N1, x1, y1, h1⟩ := hA
  obtain ⟨N2, x2, y2, h2⟩ := hB
  refine ⟨N1 + N2, Fin.append x1 x2, Fin.append y1 y2, fun p q => ?_⟩
  rw [Fin.sum_univ_add, Matrix.add_apply, h1, h2]
  simp only [Fin.append_left, Fin.append_right]

theorem in1243_sep_smul (dA dB : ℕ) (c : ℝ) (hc : 0 ≤ c) (A : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hA : matrix_is_separable dA dB A) : matrix_is_separable dA dB ((c : ℂ) • A) := by
  obtain ⟨N, x, y, h⟩ := hA
  refine ⟨N, fun i a => (Real.sqrt c : ℂ) * x i a, y, fun p q => ?_⟩
  rw [Matrix.smul_apply, h, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← hs]
  ring

theorem in1243_sep_sum (dA dB : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (h : ∀ i ∈ s, matrix_is_separable dA dB (f i)) : matrix_is_separable dA dB (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ => 0, fun _ _ => 0, fun p q => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact in1243_sep_add _ _ _ _ (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem in1243_choi_linear (d : ℕ) (r : ZMod d) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (σ : ι → Matrix (Fin d) (Fin d) ℂ) :
    prime_convolution_choi d r (∑ i ∈ s, (c i : ℂ) • σ i) =
      ∑ i ∈ s, (c i : ℂ) • prime_convolution_choi d r (σ i) := by
  ext x y
  simp only [prime_convolution_choi, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hite : ∀ (P : Prop) [Decidable P] (g : ι → ℂ),
      (if P then ∑ i ∈ s, g i else 0) = ∑ i ∈ s, if P then g i else 0 := by
    intro P _ g; split_ifs <;> simp
  simp only [hite, Finset.mul_sum]
  calc _ = ∑ j : Fin d, ∑ i ∈ s, ∑ l : Fin d, (1 / (d : ℂ)) * (if ((x.2 : ℕ) : ZMod d) = r * ((x.1 : ℕ) : ZMod d) + ((j : ℕ) : ZMod d) ∧
        ((y.2 : ℕ) : ZMod d) = r * ((y.1 : ℕ) : ZMod d) + ((l : ℕ) : ZMod d) ∧
        ((x.1 : ℕ) : ZMod d) + ((j : ℕ) : ZMod d) = ((y.1 : ℕ) : ZMod d) + ((l : ℕ) : ZMod d)
        then (c i : ℂ) * σ i j l else 0) := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> ring

open Fin.CommRing in
theorem in1243_twirl_sep (n : ℕ) (r : Fin (n+2)) (a b : Fin (n+2) → ℝ) :
    matrix_is_separable (n+2) (n+2) (prime_convolution_choi (n+2) r (Matrix.of fun j l =>
      ((∑ i, a i * b (r * i + j) * a (i + j - l) * b (r * (i + j - l) + l) : ℝ) : ℂ))) := by
  refine ⟨(n+2) * (n+2),
    fun k i => (1 / ((n+2 : ℕ) : ℂ)) * (a (i - (finProdFinEquiv.symm k).1) : ℂ) *
      ZMod.stdAddChar (N := n+2) (((finProdFinEquiv.symm k).2 * ((1 - r) * i) : Fin (n+2))),
    fun k i => (b (i - r * (finProdFinEquiv.symm k).1) : ℂ) *
      ZMod.stdAddChar (N := n+2) (((finProdFinEquiv.symm k).2 * i : Fin (n+2))), fun p q => ?_⟩
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  have hN : ((n+2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  -- the right side
  have hR : ∀ x : Fin (n+2), (∑ c : Fin (n+2),
      (1 / ((n+2 : ℕ) : ℂ)) * (a (p.1 - x) : ℂ) * ZMod.stdAddChar (N := n+2) ((c * ((1 - r) * p.1) : Fin (n+2))) *
        star ((1 / ((n+2 : ℕ) : ℂ)) * (a (q.1 - x) : ℂ) * ZMod.stdAddChar (N := n+2) ((c * ((1 - r) * q.1) : Fin (n+2)))) *
      ((b (p.2 - r * x) : ℂ) * ZMod.stdAddChar (N := n+2) ((c * p.2 : Fin (n+2))) *
        star ((b (q.2 - r * x) : ℂ) * ZMod.stdAddChar (N := n+2) ((c * q.2 : Fin (n+2)))))) =
      (1 / ((n+2 : ℕ) : ℂ)) * (if (1 - r) * p.1 + p.2 = (1 - r) * q.1 + q.2 then
        ((a (p.1 - x) * a (q.1 - x) * b (p.2 - r * x) * b (q.2 - r * x) : ℝ) : ℂ) else 0) := by
    intro x
    have hc : ∀ c : Fin (n+2), (1 / ((n+2 : ℕ) : ℂ)) * (a (p.1 - x) : ℂ) * ZMod.stdAddChar (N := n+2) ((c * ((1 - r) * p.1) : Fin (n+2))) *
        star ((1 / ((n+2 : ℕ) : ℂ)) * (a (q.1 - x) : ℂ) * ZMod.stdAddChar (N := n+2) ((c * ((1 - r) * q.1) : Fin (n+2)))) *
      ((b (p.2 - r * x) : ℂ) * ZMod.stdAddChar (N := n+2) ((c * p.2 : Fin (n+2))) *
        star ((b (q.2 - r * x) : ℂ) * ZMod.stdAddChar (N := n+2) ((c * q.2 : Fin (n+2))))) =
        (1 / ((n+2 : ℕ) : ℂ)) * (1 / ((n+2 : ℕ) : ℂ)) *
          ((a (p.1 - x) * a (q.1 - x) * b (p.2 - r * x) * b (q.2 - r * x) : ℝ) : ℂ) *
          ZMod.stdAddChar (N := n+2) ((c * (((1 - r) * p.1 + p.2) - ((1 - r) * q.1 + q.2)) : Fin (n+2))) := by
      intro c
      simp only [star_mul', in1243_chi_star, Complex.star_def, Complex.conj_ofReal, map_div₀, map_one,
        Complex.conj_natCast]
      have e : c * (((1 - r) * p.1 + p.2) - ((1 - r) * q.1 + q.2)) =
          c * ((1 - r) * p.1) + -(c * ((1 - r) * q.1)) + (c * p.2 + -(c * q.2)) := by ring
      rw [e, in1243_chi_add, in1243_chi_add, in1243_chi_add]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun c _ => hc c, ← Finset.mul_sum, in1243_chi_sum]
    by_cases hm : (1 - r) * p.1 + p.2 = (1 - r) * q.1 + q.2
    · rw [if_pos (sub_eq_zero.mpr hm), if_pos hm]
      field_simp
    · rw [if_neg (fun h => hm (sub_eq_zero.mp h)), if_neg hm]
      simp
  rw [Finset.sum_congr rfl fun x _ => hR x, ← Finset.mul_sum]
  rw [in1243b_entry]
  congr 1
  rw [Finset.sum_eq_single (p.2 - r * p.1)]
  · rw [Finset.sum_eq_single (q.2 - r * q.1)]
    · by_cases hm : (1 - r) * p.1 + p.2 = (1 - r) * q.1 + q.2
      · have hc : p.2 = r * p.1 + (p.2 - r * p.1) ∧ q.2 = r * q.1 + (q.2 - r * q.1) ∧
            p.1 + (p.2 - r * p.1) = q.1 + (q.2 - r * q.1) :=
          ⟨by ring, by ring, by linear_combination hm⟩
        rw [if_pos hc, Matrix.of_apply]
        simp only [if_pos hm]
        rw [← Complex.ofReal_sum]
        congr 1
        rw [← Equiv.sum_comp (Equiv.subLeft p.1)]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Equiv.subLeft_apply]
        have e1 : r * (p.1 - x) + (p.2 - r * p.1) = p.2 - r * x := by ring
        have e2 : p.1 - x + (p.2 - r * p.1) - (q.2 - r * q.1) = q.1 - x := by linear_combination hm
        rw [e1, e2]
        have e3 : r * (q.1 - x) + (q.2 - r * q.1) = q.2 - r * x := by ring
        rw [e3]
        ring
      · rw [if_neg]
        · simp [hm]
        rintro ⟨_, _, h⟩
        exact hm (by linear_combination h)
    · intro l _ hl
      rw [if_neg]
      rintro ⟨_, h, _⟩
      exact hl (by rw [h]; ring)
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg]
    rintro ⟨h, _, _⟩
    exact hj (by rw [h]; ring)
  · intro h; exact absurd (Finset.mem_univ _) h

open Fin.CommRing in
theorem in1243_eint : ∀ (k : Fin 9) (j l : Fin 5),
    (∑ i : Fin 5, ((![![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) i *
        ((![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![1, -1, 1, 1, 0], ![1, 1, -1, 1, 0], ![0, 1, 0, 0, 0], ![0, 1, -1, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) (2 * i + j) *
        ((![![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) (i + j - l) *
        ((![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![1, -1, 1, 1, 0], ![1, 1, -1, 1, 0], ![0, 1, 0, 0, 0], ![0, 1, -1, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) (2 * (i + j - l) + l)) =
      (![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1]], ![![2, 1, 0, 0, 1], ![1, 2, -1, 0, 0], ![0, -1, 1, 0, 0], ![0, 0, 0, 2, 0], ![1, 0, 0, 0, 1]], ![![2, 1, 0, 0, -1], ![1, 2, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1]]] : Fin 9 → Fin 5 → Fin 5 → ℤ) k j l := by
  decide

theorem in1243_env_decomp (t : ℝ) (j l : Fin 5) :
    two_level_environment 5 (1/5) t j l = ∑ k : Fin 9, ((((![(1 - 3 * t) / 5, (1 - 3 * t) / 5, (1 - 3 * t) / 5, (1 - 3 * t) / 5, (1 - 3 * t) / 5, t / 10, t / 10, 3 * t / 5, t / 5] : Fin 9 → ℝ) k) : ℝ) : ℂ) *
      (((![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1]], ![![2, 1, 0, 0, 1], ![1, 2, -1, 0, 0], ![0, -1, 1, 0, 0], ![0, 0, 0, 2, 0], ![1, 0, 0, 0, 1]], ![![2, 1, 0, 0, -1], ![1, 2, 1, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 1]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1]]] : Fin 9 → Fin 5 → Fin 5 → ℤ) k j l : ℤ) : ℂ) := by
  have hs : Real.sqrt (1 - 1/5) = 2 * Real.sqrt (1/5) := by
    rw [show (1:ℝ) - 1/5 = 2^2 * (1/5) by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hss : ((Real.sqrt (1/5) : ℝ) : ℂ) * ((Real.sqrt (1/5) : ℝ) : ℂ) = 1/5 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have h5 : ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ ^ 2 = 1/5 := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  simp only [two_level_environment, Matrix.of_apply, hs]
  fin_cases j <;> fin_cases l <;>
    simp [Fin.sum_univ_succ, h5] <;>
    first | ring1 | linear_combination t * h5 | linear_combination 2 * t * h5 | linear_combination 4 * t * h5


open Fin.CommRing in
theorem in1243_env_decomp2 (t : ℝ) :
    two_level_environment 5 (1/5) t = ∑ k : Fin 9, ((((![(1 - 3 * t) / 5, (1 - 3 * t) / 5, (1 - 3 * t) / 5, (1 - 3 * t) / 5, (1 - 3 * t) / 5, t / 10, t / 10, 3 * t / 5, t / 5] : Fin 9 → ℝ) k) : ℝ) : ℂ) •
        Matrix.of fun j l => ((∑ i : Fin 5, ((((![![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) i : ℤ) : ℝ) *
          ((((![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![1, -1, 1, 1, 0], ![1, 1, -1, 1, 0], ![0, 1, 0, 0, 0], ![0, 1, -1, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) (2 * i + j) : ℤ) : ℝ) *
          ((((![![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) (i + j - l) : ℤ) : ℝ) *
          ((((![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![1, -1, 1, 1, 0], ![1, 1, -1, 1, 0], ![0, 1, 0, 0, 0], ![0, 1, -1, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) (2 * (i + j - l) + l) : ℤ) : ℝ) : ℝ) : ℂ) := by
  ext j l
  rw [in1243_env_decomp, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← in1243_eint]
  push_cast
  rfl
open Fin.CommRing in
theorem in1243_five_sep (t : ℝ) (h0 : 0 ≤ t) (ht : t ≤ 1 / 3) :
    matrix_is_separable 5 5 (prime_convolution_choi 5 2 (two_level_environment 5 (1/5) t)) := by
  rw [in1243_env_decomp2, in1243_choi_linear]
  refine in1243_sep_sum _ _ _ _ fun k _ => in1243_sep_smul _ _ _ ?_ _ ?_
  · fin_cases k <;> simp <;> linarith
  · exact in1243_twirl_sep 3 2 (fun i => ((((![![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, -1, 0, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) i : ℤ) : ℝ))
      (fun i => ((((![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![1, -1, 1, 1, 0], ![1, 1, -1, 1, 0], ![0, 1, 0, 0, 0], ![0, 1, -1, 0, 0]] : Fin 9 → Fin 5 → ℤ) k) i : ℤ) : ℝ))

theorem prime_convolution_five_two_fifth_entanglement_breaking_iff (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    matrix_is_separable 5 5 (prime_convolution_choi 5 2 (two_level_environment 5 (1/5) t)) ↔ t ≤ 1 / 3 := by
  constructor
  · intro h
    have key := prime_convolution_separable_imp_threshold 5 (by norm_num) le_rfl 2 (by decide) (by decide)
      (by decide) (1/5) t (by norm_num) (by norm_num) h0 h1 h
    have hsq : Real.sqrt (1/5 * (1 - 1/5)) = 2/5 := by
      rw [show (1:ℝ)/5 * (1 - 1/5) = (2/5)^2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [hsq] at key
    norm_num at key
    linarith
  · exact in1243_five_sep t h0
