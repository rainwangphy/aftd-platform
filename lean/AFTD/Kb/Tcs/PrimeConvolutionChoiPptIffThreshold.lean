import AFTD.Prelude
import AFTD.Kb.Tcs.PrimeConvolutionChoi
import AFTD.Kb.Tcs.TwoLevelEnvironment

/-!
# prime_convolution_choi_ppt_iff_threshold

Topic: quantum   Node: 1107ceb153b1

Provenance: original. Related work: OP-2466 (proposed here; it builds on the qutrit convolution channels of arXiv:2609.16200, whose Theorem 8 gives the exact PPT and entanglement-breaking threshold 2/5 on a balanced two-level qutrit slice, and on arXiv:2611.09594, which shows PPT and entanglement breaking differ for another convolution environment). The screen's signal on the entry (experiments 42058, 42060; boundary reproduced for this definition in experiment 42119): the partial transpose splits into 2×2 blocks carrying the coherence.

Let d be a prime with d ≥ 5, r ∈ ZMod d with r ≠ 0, r ≠ 1 and 2r ≠ 1 (r is not the inverse of 2), and p, t real numbers in [0, 1]. Let J = prime_convolution_choi d r (two_level_environment d p t) and let J^Γ be its partial transpose on the second factor, the matrix indexed by Fin d × Fin d whose (x, y) entry is J (x.1, y.2) (y.1, x.2). Then J^Γ is positive semidefinite if and only if t ≤ 1/(1 + d·√(p(1 − p))).
-/

open Fin.CommRing in
theorem in1243_cast (n : ℕ) (a : Fin (n+2)) : (((a : ℕ) : ZMod (n+2))) = a :=
  ZMod.natCast_zmod_val (n := n+2) a

open Fin.CommRing in
theorem in1243_entry (n : ℕ) (r : Fin (n+2)) (σ : Matrix (Fin (n+2)) (Fin (n+2)) ℂ)
    (x y : Fin (n+2) × Fin (n+2)) :
    prime_convolution_choi (n+2) r σ x y = (1 / ((n+2 : ℕ) : ℂ)) * ∑ j : Fin (n+2), ∑ l : Fin (n+2),
      if x.2 = r * x.1 + j ∧ y.2 = r * y.1 + l ∧ x.1 + j = y.1 + l then σ j l else 0 := by
  simp only [prime_convolution_choi, Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have e : ∀ a : Fin (n+2), (((a : ℕ) : ZMod (n+2))) = a := in1243_cast n
  erw [e x.1, e x.2, e y.1, e y.2, e j, e l]
  rfl

open Fin.CommRing in
theorem in1243_psi_sum (n : ℕ) (a b : ℝ) (F : Fin (n+2) → ℂ) :
    ∑ j : Fin (n+2), (((if (j : ℕ) = 0 then a else if (j : ℕ) = 1 then b else 0 : ℝ) : ℂ)) * F j =
      (a : ℂ) * F 0 + (b : ℂ) * F 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp

open Fin.CommRing in
theorem in1243_inner (n : ℕ) (r j l : Fin (n+2)) (x : Fin (n+2) × Fin (n+2) → ℂ) :
    (∑ p : Fin (n+2) × Fin (n+2), ∑ q : Fin (n+2) × Fin (n+2),
      if q.2 = r * p.1 + j ∧ p.2 = r * q.1 + l ∧ p.1 + j = q.1 + l then star (x p) * x q else 0) =
    ∑ k : Fin (n+2), star (x (k, r * (k + j - l) + l)) * x (k + j - l, r * k + j) := by
  have h1 : ∀ p : Fin (n+2) × Fin (n+2), (∑ q : Fin (n+2) × Fin (n+2),
      if q.2 = r * p.1 + j ∧ p.2 = r * q.1 + l ∧ p.1 + j = q.1 + l then star (x p) * x q else 0) =
      if p.2 = r * (p.1 + j - l) + l then star (x p) * x (p.1 + j - l, r * p.1 + j) else 0 := by
    intro p
    rw [Finset.sum_eq_single (p.1 + j - l, r * p.1 + j)]
    · have : p.1 + j = p.1 + j - l + l := by ring
      by_cases h : p.2 = r * (p.1 + j - l) + l
      · rw [if_pos ⟨rfl, h, this⟩, if_pos h]
      · rw [if_neg (fun hh => h hh.2.1), if_neg h]
    · intro q _ hq
      rw [if_neg]
      rintro ⟨ha, _, hc⟩
      apply hq
      have : q.1 = p.1 + j - l := by rw [hc]; ring
      exact Prod.ext this ha
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [h1]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

open Fin.CommRing in
theorem in1243_qform (n : ℕ) (r : Fin (n+2)) (σ : Matrix (Fin (n+2)) (Fin (n+2)) ℂ)
    (x : Fin (n+2) × Fin (n+2) → ℂ) :
    dotProduct (star x) (Matrix.mulVec (Matrix.of fun (p q : Fin (n+2) × Fin (n+2)) =>
        prime_convolution_choi (n+2) r σ (p.1, q.2) (q.1, p.2)) x) =
      (1 / ((n+2 : ℕ) : ℂ)) * ∑ j : Fin (n+2), ∑ l : Fin (n+2), σ j l *
        ∑ k : Fin (n+2), star (x (k, r * (k + j - l) + l)) * x (k + j - l, r * k + j) := by
  set N : ℂ := ((n+2 : ℕ) : ℂ)
  let F : Fin (n+2) × Fin (n+2) → Fin (n+2) × Fin (n+2) → Fin (n+2) → Fin (n+2) → ℂ :=
    fun p q j l => (1 / N) * (if q.2 = r * p.1 + j ∧ p.2 = r * q.1 + l ∧ p.1 + j = q.1 + l
      then σ j l * (star (x p) * x q) else 0)
  have L : dotProduct (star x) (Matrix.mulVec (Matrix.of fun (p q : Fin (n+2) × Fin (n+2)) =>
        prime_convolution_choi (n+2) r σ (p.1, q.2) (q.1, p.2)) x) =
      ∑ p, ∑ q, ∑ j, ∑ l, F p q j l := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, in1243_entry, Pi.star_apply,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [F]
    split_ifs <;> ring
  have R : (1 / N) * ∑ j : Fin (n+2), ∑ l : Fin (n+2), σ j l *
        ∑ k : Fin (n+2), star (x (k, r * (k + j - l) + l)) * x (k + j - l, r * k + j) =
      ∑ j, ∑ l, ∑ p, ∑ q, F p q j l := by
    simp only [← in1243_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [F]
    split_ifs <;> ring
  rw [L, R]
  calc ∑ p, ∑ q, ∑ j, ∑ l, F p q j l = ∑ p, ∑ j, ∑ q, ∑ l, F p q j l :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ j, ∑ l, ∑ q, F p q j l :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ p, ∑ l, ∑ q, F p q j l := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ p, ∑ q, F p q j l := Finset.sum_congr rfl fun j _ => Finset.sum_comm

open Fin.CommRing in
theorem in1243_qform_env (n : ℕ) (r : Fin (n+2)) (p t : ℝ) (x : Fin (n+2) × Fin (n+2) → ℂ) :
    dotProduct (star x) (Matrix.mulVec (Matrix.of fun (a b : Fin (n+2) × Fin (n+2)) =>
        prime_convolution_choi (n+2) r (two_level_environment (n+2) p t) (a.1, b.2) (b.1, a.2)) x) =
      (1 / ((n+2 : ℕ) : ℂ)) * (((1 - t) / ((n+2 : ℕ) : ℝ) : ℝ) * ∑ a, star (x a) * x a +
        (t : ℂ) * ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) * ∑ k, star (x (k, r * k)) * x (k, r * k) +
          (Real.sqrt p : ℂ) * (Real.sqrt (1 - p) : ℂ) *
            (∑ k, star (x (k + 1, r * k + 1)) * x (k, r * (k + 1)) +
             ∑ k, star (x (k, r * (k + 1))) * x (k + 1, r * k + 1)) +
          (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) *
            ∑ k, star (x (k, r * k + 1)) * x (k, r * k + 1))) := by
  rw [in1243_qform]
  congr 1
  set T : Fin (n+2) → Fin (n+2) → ℂ := fun j l =>
    ∑ k : Fin (n+2), star (x (k, r * (k + j - l) + l)) * x (k + j - l, r * k + j) with hT
  set ψ : Fin (n+2) → ℝ := fun j => if (j : ℕ) = 0 then Real.sqrt p else if (j : ℕ) = 1 then Real.sqrt (1 - p) else 0 with hψ
  have hσ : ∀ j l, two_level_environment (n+2) p t j l * T j l =
      (((if j = l then (1 - t) / ((n+2 : ℕ) : ℝ) else 0 : ℝ)) : ℂ) * T j l +
        (t : ℂ) * (((ψ j : ℝ) : ℂ) * (((ψ l : ℝ) : ℂ) * T j l)) := by
    intro j l
    simp only [two_level_environment, Matrix.of_apply, hψ]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => hσ j l]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∀ j : Fin (n+2), ∑ l : Fin (n+2), (((if j = l then (1 - t) / ((n+2 : ℕ) : ℝ) else 0 : ℝ)) : ℂ) * T j l
      = (((1 - t) / ((n+2 : ℕ) : ℝ) : ℝ) : ℂ) * T j j := by
    intro j
    simp only [apply_ite (fun z : ℝ => (z : ℂ)), Complex.ofReal_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  simp only [h1, ← Finset.mul_sum]
  have h2 : ∑ j : Fin (n+2), T j j = ∑ a, star (x a) * x a := by
    simp only [hT, add_sub_cancel_right]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Equiv.sum_comp (Equiv.addLeft (r * k)) (fun b => star (x (k, b)) * x (k, b))
  rw [h2]
  congr 1
  rw [in1243_psi_sum, in1243_psi_sum, in1243_psi_sum]
  have h01 : T 0 1 = ∑ k, star (x (k + 1, r * k + 1)) * x (k, r * (k + 1)) := by
    simp only [hT]
    rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin (n+2)))]
    simp [add_sub_cancel_right]
  have h00 : T 0 0 = ∑ k, star (x (k, r * k)) * x (k, r * k) := by simp [hT]
  have h11 : T 1 1 = ∑ k, star (x (k, r * k + 1)) * x (k, r * k + 1) := by simp [hT]
  have h10 : T 1 0 = ∑ k, star (x (k, r * (k + 1))) * x (k + 1, r * k + 1) := by simp [hT]
  rw [h00, h01, h10, h11]
  ring

open Fin.CommRing in
theorem in1243_pairs (n : ℕ) (r : Fin (n+2)) (hr2 : 2 * r ≠ 1)
    (f : Fin (n+2) × Fin (n+2) → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ k, (f (k, r * (k + 1)) + f (k + 1, r * k + 1)) ≤ ∑ a, f a := by
  let e : Fin (n+2) ⊕ Fin (n+2) → Fin (n+2) × Fin (n+2) := fun z =>
    match z with
    | Sum.inl k => (k, r * (k + 1))
    | Sum.inr k => (k + 1, r * k + 1)
  have he : Function.Injective e := by
    have key : ∀ k k' : Fin (n+2), (k, r * (k + 1)) ≠ (k' + 1, r * k' + 1) := by
      intro k k' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      apply hr2
      linear_combination h2
    rintro (k | k) (k' | k') h
    · simp only [e, Prod.mk.injEq] at h; rw [h.1]
    · exact absurd h (key k k')
    · exact absurd h.symm (key k' k)
    · simp only [e, Prod.mk.injEq] at h; rw [add_right_cancel h.1]
  rw [Finset.sum_add_distrib]
  have : ∑ k, f (k, r * (k + 1)) + ∑ k, f (k + 1, r * k + 1) = ∑ z, f (e z) := by
    rw [Fintype.sum_sum_type]
  rw [this, ← Finset.sum_image (fun a _ b _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => hf a

open Fin.CommRing in
theorem in1243_env_star (n : ℕ) (p t : ℝ) (j l : Fin (n+2)) :
    star (two_level_environment (n+2) p t j l) = two_level_environment (n+2) p t l j := by
  simp only [two_level_environment, Matrix.of_apply, star_add, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  by_cases h : j = l
  · subst h; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

open Fin.CommRing in
theorem in1243_hermitian (n : ℕ) (r : Fin (n+2)) (p t : ℝ) :
    (Matrix.of fun (a b : Fin (n+2) × Fin (n+2)) =>
        prime_convolution_choi (n+2) r (two_level_environment (n+2) p t) (a.1, b.2) (b.1, a.2)).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, in1243_entry, star_mul', star_sum]
  congr 1
  · simp
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [apply_ite star, star_zero, in1243_env_star]
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3.symm⟩

open scoped ComplexOrder in
open Fin.CommRing in
theorem in1243_core (n : ℕ) (r : Fin (n+2)) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr2 : 2 * r ≠ 1)
    (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht0 : 0 ≤ t) :
    (Matrix.of fun (a b : Fin (n+2) × Fin (n+2)) =>
        prime_convolution_choi (n+2) r (two_level_environment (n+2) p t) (a.1, b.2) (b.1, a.2)).PosSemidef ↔
      t ≤ 1 / (1 + ((n+2 : ℕ) : ℝ) * Real.sqrt (p * (1 - p))) := by
  have hN : (0 : ℝ) < ((n+2 : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0
  have hc : Real.sqrt (1 - p) * Real.sqrt (1 - p) = 1 - p := Real.mul_self_sqrt (by linarith)
  have hsc : Real.sqrt (p * (1 - p)) = Real.sqrt p * Real.sqrt (1 - p) := Real.sqrt_mul hp0 _
  have hsc0 : 0 ≤ Real.sqrt p * Real.sqrt (1 - p) := by positivity
  have hthr : t ≤ 1 / (1 + ((n+2 : ℕ) : ℝ) * Real.sqrt (p * (1 - p))) ↔
      t * (Real.sqrt p * Real.sqrt (1 - p)) ≤ (1 - t) / ((n+2 : ℕ) : ℝ) := by
    rw [hsc, le_div_iff₀ (by positivity), le_div_iff₀ hN]
    constructor <;> intro h <;> nlinarith
  rw [hthr]
  -- the quadratic form as a real number
  have hQ : ∀ x : Fin (n+2) × Fin (n+2) → ℂ,
      dotProduct (star x) (Matrix.mulVec (Matrix.of fun (a b : Fin (n+2) × Fin (n+2)) =>
        prime_convolution_choi (n+2) r (two_level_environment (n+2) p t) (a.1, b.2) (b.1, a.2)) x) =
      ((1 / ((n+2 : ℕ) : ℝ) * ((1 - t) / ((n+2 : ℕ) : ℝ) * ∑ a, Complex.normSq (x a) +
        t * (p * ∑ k, Complex.normSq (x (k, r * k)) +
          Real.sqrt p * Real.sqrt (1 - p) *
            (2 * (∑ k, star (x (k, r * (k + 1))) * x (k + 1, r * k + 1)).re) +
          (1 - p) * ∑ k, Complex.normSq (x (k, r * k + 1)))) : ℝ) : ℂ) := by
    intro x
    rw [in1243_qform_env]
    have hstar : ∑ k, star (x (k + 1, r * k + 1)) * x (k, r * (k + 1)) =
        star (∑ k, star (x (k, r * (k + 1))) * x (k + 1, r * k + 1)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [star_mul', star_star, mul_comm]
    rw [hstar]
    have hre : ∀ z : ℂ, star z + z = ((2 * z.re : ℝ) : ℂ) := by
      intro z
      rw [Complex.star_def, add_comm, Complex.add_conj]
    have hn : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      intro z
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    rw [hre]
    simp only [hn]
    have hs' : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
      rw [← Complex.ofReal_mul, hs]
    have hc' : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hc]
    rw [hs', hc']
    push_cast
    ring
  constructor
  · -- necessity: test vector e_(0,r) - e_(1,1)
    intro hpsd
    by_contra hlt'
    have hlt := lt_of_not_ge hlt'
    have h01 : (0 : Fin (n+2)) ≠ 1 := by
      intro h; have := congrArg Fin.val h; simp at this
    let u : Fin (n+2) × Fin (n+2) := (0, r)
    let v : Fin (n+2) × Fin (n+2) := (1, 1)
    have huv : u ≠ v := fun h => h01 (congrArg Prod.fst h)
    let x : Fin (n+2) × Fin (n+2) → ℂ := fun a => if a = u then 1 else if a = v then -1 else 0
    have hxu : x u = 1 := by simp [x]
    have hxv : x v = -1 := by simp [x, huv.symm]
    have hx0 : ∀ a, a ≠ u → a ≠ v → x a = 0 := by intro a h1 h2; simp [x, h1, h2]
    have hX : ∑ a, Complex.normSq (x a) = 2 := by
      rw [Fintype.sum_eq_add u v huv (fun a ⟨h1, h2⟩ => by rw [hx0 a h1 h2, map_zero]), hxu, hxv]
      simp; norm_num
    have hA : ∑ k, Complex.normSq (x (k, r * k)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hx0, map_zero]
      · intro h; simp only [u, Prod.mk.injEq] at h; obtain ⟨rfl, h⟩ := h
        exact hr0 (by simpa using h.symm)
      · intro h; simp only [v, Prod.mk.injEq] at h; obtain ⟨rfl, h⟩ := h
        exact hr1 (by simpa using h)
    have hB : ∑ k, Complex.normSq (x (k, r * k + 1)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hx0, map_zero]
      · intro h; simp only [u, Prod.mk.injEq] at h; obtain ⟨rfl, h⟩ := h
        exact hr1 (by simpa using h.symm)
      · intro h; simp only [v, Prod.mk.injEq] at h; obtain ⟨rfl, h⟩ := h
        exact hr0 (by simpa using h)
    have hT : ∑ k, star (x (k, r * (k + 1))) * x (k + 1, r * k + 1) = -1 := by
      rw [Fintype.sum_eq_single 0]
      · have e1 : ((0 : Fin (n+2)), r * (0 + 1)) = u := by simp [u]
        have e2 : ((0 : Fin (n+2)) + 1, r * 0 + 1) = v := by simp [v]
        rw [e1, e2, hxu, hxv]; simp
      · intro k hk
        rw [hx0 (k, r * (k + 1)), star_zero, zero_mul]
        · intro h; simp only [u, Prod.mk.injEq] at h; exact hk h.1
        · intro h; simp only [v, Prod.mk.injEq] at h; obtain ⟨rfl, h⟩ := h
          apply hr2; linear_combination h
    have hq := hpsd.dotProduct_mulVec_nonneg x
    rw [hQ x, hX, hA, hB, hT, Complex.zero_le_real] at hq
    have hm1 : (-1 : ℂ).re = -1 := by simp
    rw [hm1] at hq
    have hinv : (0 : ℝ) < 1 / ((n+2 : ℕ) : ℝ) := by positivity
    have key := (mul_nonneg_iff_of_pos_left hinv).mp hq
    nlinarith [key, hlt]
  · -- sufficiency
    intro hle
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (in1243_hermitian n r p t) fun x => ?_
    rw [hQ x, Complex.zero_le_real]
    set S := ∑ k, star (x (k, r * (k + 1))) * x (k + 1, r * k + 1)
    have hX0 : 0 ≤ ∑ a, Complex.normSq (x a) := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
    have hA0 : 0 ≤ ∑ k, Complex.normSq (x (k, r * k)) := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
    have hB0 : 0 ≤ ∑ k, Complex.normSq (x (k, r * k + 1)) := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
    have hS : 2 * |S.re| ≤ ∑ a, Complex.normSq (x a) := by
      have h1 : |S.re| ≤ ∑ k, ‖x (k, r * (k + 1))‖ * ‖x (k + 1, r * k + 1)‖ := by
        simp only [S, Complex.re_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, norm_star]
      have h2 : ∀ k, 2 * (‖x (k, r * (k + 1))‖ * ‖x (k + 1, r * k + 1)‖) ≤
          Complex.normSq (x (k, r * (k + 1))) + Complex.normSq (x (k + 1, r * k + 1)) := by
        intro k
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg (‖x (k, r * (k + 1))‖ - ‖x (k + 1, r * k + 1)‖)]
      have h3 := in1243_pairs n r hr2 (fun a => Complex.normSq (x a)) (fun a => Complex.normSq_nonneg _)
      have h4 : 2 * ∑ k, ‖x (k, r * (k + 1))‖ * ‖x (k + 1, r * k + 1)‖ ≤
          ∑ k, (Complex.normSq (x (k, r * (k + 1))) + Complex.normSq (x (k + 1, r * k + 1))) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun k _ => h2 k
      linarith
    have hneg : -|S.re| ≤ S.re := neg_abs_le _
    apply mul_nonneg (by positivity)
    have hp1' : 0 ≤ 1 - p := by linarith
    have hneg' : 0 ≤ |S.re| + S.re := by linarith
    nlinarith [mul_nonneg ht0 hsc0, mul_nonneg (mul_nonneg ht0 hsc0) hneg',
      mul_nonneg ht0 (mul_nonneg hp0 hA0), mul_nonneg ht0 (mul_nonneg hp1' hB0),
      mul_nonneg (sub_nonneg.mpr hle) hX0, mul_nonneg (mul_nonneg ht0 hsc0) (sub_nonneg.mpr hS)]

theorem prime_convolution_choi_ppt_iff_threshold :
    ∀ d : ℕ, d.Prime → 5 ≤ d → ∀ r : ZMod d, r ≠ 0 → r ≠ 1 → 2 * r ≠ 1 →
      ∀ p t : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ t → t ≤ 1 →
        ((open scoped ComplexOrder in (Matrix.of fun (x y : Fin d × Fin d) =>
            prime_convolution_choi d r (two_level_environment d p t) (x.1, y.2) (y.1, x.2)).PosSemidef) ↔
          t ≤ 1 / (1 + d * Real.sqrt (p * (1 - p)))) := by
  intro d _ h5 r hr0 hr1 hr2 p t hp0 hp1 ht0 _
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  exact in1243_core n r hr0 hr1 hr2 p t hp0 hp1 ht0
