import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareGuessFn
import AFTD.Kb.Tcs.MagicSquareThresholdBeta0
import AFTD.Kb.Tcs.MagicSquareScore
import AFTD.Kb.Tcs.MagicSquareGuessFnConcaveOn
import AFTD.Kb.Tcs.MagicSquareKeyGuessSuccess
import AFTD.Kb.Tcs.MagicSquareStrategyValid
import AFTD.Kb.Tcs.IsPovm

/-!
# magic_square_guess_fn_ge_linear

Topic: quantum   Node: a464d9d45012

Provenance: formalization of a published result. Source: arXiv:2610.12001 (Exact value and rigidity of the 2x3 magic rectangle), Corollary 6.2, Eq. (26), second inequality.

For 0 ≤ δ ≤ 1 - β₀, with β₀ = (2 + √(2/3))/3 the magic-square threshold: 1 - g(β₀ + δ) ≤ 3δ / (4(1 - β₀)), where β₀ = magic_square_threshold_beta0 and g = magic_square_guess_fn, g(w) being the best guessing probability of Alice's first-row answer by a quantum adversary over strategies with score at least w.
-/

namespace MagicSquareGeLinear
open Matrix
open scoped Kronecker ComplexOrder

def Mc : Matrix (Fin 4) (Fin 4) ℤ := !![0, 1, 1, 1; -1, 0, 1, -1; -1, -1, 0, 1; -1, 1, -1, 0]

def Dv : Fin 3 → Fin 4 → ℤ := ![![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

def Zt (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℤ :=
  3 • Matrix.diagonal (Dv j) - Mc * Matrix.diagonal (Dv j) * Mc.transpose

def alpha : Fin 4 → (Fin 3 → Bool) :=
  ![![false, false, false], ![false, true, true], ![true, false, true], ![true, true, false]]

def TA (x : Fin 3) (s : Fin 3 → Bool) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i i' =>
    if x = 0 then (if s = (fun _ => false) ∧ i = i' then 3 else 0)
    else if x = 1 then (if alpha i = s ∧ i = i' then 3 else 0)
    else ∑ a : Fin 4, if alpha a = s then Mc i a * Mc i' a else 0

def bw (c : Fin 3 → Bool) : ℤ := if c 0 = false ∧ c 1 ≠ c 2 then 1 else 0

def bv (c : Fin 3 → Bool) : ℤ := if c 0 = false ∧ c 1 ≠ c 2 then (if c 1 then -1 else 1) else 0

def T0 (x : Fin 3) (s : Fin 3 → Bool) : ℤ := ∑ a : Fin 4, TA x s a a

def T1 (x j : Fin 3) (s : Fin 3 → Bool) : ℤ := ∑ a : Fin 4, ∑ a' : Fin 4, TA x s a a' * Zt j a a'

set_option maxRecDepth 100000 in
theorem TA_proj : ∀ x s, TA x s * TA x s = 3 • TA x s ∧ (TA x s).transpose = TA x s := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem TA_sum : ∀ x, ∑ s, TA x s = 3 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem TA_zero : ∀ x s, xor (xor (s 0) (s 1)) (s 2) = true → TA x s = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem TA_key : TA 0 (fun _ => false) = 3 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Zt_sq : ∀ j, Zt j * Zt j = 24 • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧ (Zt j).transpose = Zt j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bw_sum : ∑ c, bw c = 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem bv_sum : ∑ c, bv c = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem bwv_zero : ∀ c : Fin 3 → Bool, xor (xor (c 0) (c 1)) (c 2) = false → bw c = 0 ∧ bv c = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem bwv_legal : ∀ c : Fin 3 → Bool, bw c = 0 ∧ bv c = 0 ∨ bw c = 1 ∧ (bv c = 1 ∨ bv c = -1) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem win0 : (∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool,
    if s j = c x then bw c * T0 x s else 0) = 144 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem win1 : (∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool,
    if s j = c x then bv c * T1 x j s else 0) = 288 := by
  decide +kernel

noncomputable def Ac (x : Fin 3) (s : Fin 3 → Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 3 : ℂ) • (Int.castRingHom ℂ).mapMatrix (TA x s)

noncomputable def Yc (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Real.sqrt 6 : ℂ) / 12) • (Int.castRingHom ℂ).mapMatrix (Zt j)

noncomputable def Bc (j : Fin 3) (c : Fin 3 → Bool) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((bw c : ℂ) / 2) • 1 + ((bv c : ℂ) / 2) • Yc j

lemma psd3 (P : Matrix (Fin 4) (Fin 4) ℤ) (h : P * P = 3 • P ∧ P.transpose = P) :
    ((1 / 3 : ℂ) • (Int.castRingHom ℂ).mapMatrix P).PosSemidef := by
  have hc : ((1 / 3 : ℂ) • (Int.castRingHom ℂ).mapMatrix P)ᴴ = (1 / 3 : ℂ) • (Int.castRingHom ℂ).mapMatrix P := by
    ext i j
    have := congrFun (congrFun h.2 i) j
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, this]
  have hm : (1 / 3 : ℂ) • (Int.castRingHom ℂ).mapMatrix P =
      ((1 / 3 : ℂ) • (Int.castRingHom ℂ).mapMatrix P) * ((1 / 3 : ℂ) • (Int.castRingHom ℂ).mapMatrix P)ᴴ := by
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, ← map_mul, h.1, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, smul_smul]
    norm_num
  rw [hm]
  exact Matrix.posSemidef_self_mul_conjTranspose _

lemma Yc_herm (j : Fin 3) : (Yc j)ᴴ = Yc j := by
  ext a b
  have := congrFun (congrFun (Zt_sq j).2 a) b
  simp only [Matrix.transpose_apply] at this
  simp [Yc, Matrix.conjTranspose_apply, this, Complex.conj_ofReal]

lemma sqrt6_sq : ((Real.sqrt 6 : ℂ)) * (Real.sqrt 6 : ℂ) = 6 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma Yc_sq (j : Fin 3) : Yc j * Yc j = 1 := by
  rw [Yc, Matrix.smul_mul, Matrix.mul_smul, ← map_mul, (Zt_sq j).1, map_nsmul, map_one,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
  have : (Real.sqrt 6 : ℂ) / 12 * ((Real.sqrt 6 : ℂ) / 12) * ((24 : ℕ) : ℂ) = 1 := by
    have h := sqrt6_sq
    field_simp
    linear_combination 24 * h
  rw [this, one_smul]

lemma half_psd {Y : Matrix (Fin 4) (Fin 4) ℂ} (hY : Yᴴ = Y) (hY2 : Y * Y = 1) (t : ℂ)
    (ht : t = 1 ∨ t = -1) : ((1 / 2 : ℂ) • 1 + (t / 2) • Y).PosSemidef := by
  have hc : ((1 / 2 : ℂ) • 1 + (t / 2) • Y)ᴴ = (1 / 2 : ℂ) • 1 + (t / 2) • Y := by
    rcases ht with rfl | rfl <;> simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hY]
  have hm : (1 / 2 : ℂ) • 1 + (t / 2) • Y =
      ((1 / 2 : ℂ) • 1 + (t / 2) • Y) * ((1 / 2 : ℂ) • 1 + (t / 2) • Y)ᴴ := by
    rw [hc]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hY2]
    rcases ht with rfl | rfl
    · module
    · module
  rw [hm]
  exact Matrix.posSemidef_self_mul_conjTranspose _

lemma valid : magic_square_strategy_valid Ac Bc MagicSquareConcave.ρc := by
  have hρ := MagicSquareConcave.perf_valid.2.2.2.2
  refine ⟨fun x => ⟨fun s => psd3 _ (TA_proj x s), ?_⟩, fun x s hs => ?_,
    fun j => ⟨fun c => ?_, ?_⟩, fun j c hc => ?_, hρ.1, hρ.2⟩
  · simp only [Ac]
    rw [← Finset.smul_sum, ← map_sum, TA_sum, map_nsmul, map_one, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  · simp [Ac, TA_zero x s hs]
  · rcases bwv_legal c with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Bc, h1, h2]
      simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 4) (Fin 4) ℂ).PosSemidef)
    · simp only [Bc, h1, Int.cast_one]
      exact half_psd (Yc_herm j) (Yc_sq j) (bv c : ℂ) (by rcases h2 with h | h <;> simp [h])
  · simp only [Bc]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_div, ← Finset.sum_div,
      ← Int.cast_sum, ← Int.cast_sum, bw_sum, bv_sum]
    norm_num
  · obtain ⟨h1, h2⟩ := bwv_zero c hc
    simp [Bc, h1, h2]

lemma cell (x j : Fin 3) (s c : Fin 3 → Bool) :
    (((Ac x s ⊗ₖ Bc j c) ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) * MagicSquareConcave.ρc).trace.re =
      1 / 12 * ((bw c : ℝ) / 2 * (T0 x s : ℝ) + (bv c : ℝ) * Real.sqrt 6 / 24 * (T1 x j s : ℝ)) := by
  rw [MagicSquareConcave.perf_tr_rho]
  have : (1 / 4 : ℂ) * ∑ a : Fin 4, ∑ a' : Fin 4, Ac x s a a' * Bc j c a a' =
      ((1 / 12 * ((bw c : ℝ) / 2 * (T0 x s : ℝ) + (bv c : ℝ) * Real.sqrt 6 / 24 * (T1 x j s : ℝ)) : ℝ) : ℂ) := by
    simp only [Ac, Bc, Yc, T0, T1, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast, smul_eq_mul, Fin.sum_univ_four]
    push_cast
    simp
    ring
  rw [this, Complex.ofReal_re]

lemma score_eq : magic_square_score Ac Bc MagicSquareConcave.ρc = 2 / 3 + Real.sqrt 6 / 9 := by
  have h0 := congrArg (Int.cast : ℤ → ℝ) win0
  have h1 := congrArg (Int.cast : ℤ → ℝ) win1
  push_cast at h0 h1
  rw [magic_square_score]
  simp only [cell]
  have : (∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool,
      if s j = c x then 1 / 12 * ((bw c : ℝ) / 2 * (T0 x s : ℝ) + (bv c : ℝ) * Real.sqrt 6 / 24 * (T1 x j s : ℝ))
      else 0) =
      1 / 24 * (∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool,
        if s j = c x then (bw c : ℝ) * (T0 x s : ℝ) else 0) +
      Real.sqrt 6 / 288 * (∑ x : Fin 3, ∑ j : Fin 3, ∑ s : Fin 3 → Bool, ∑ c : Fin 3 → Bool,
        if s j = c x then (bv c : ℝ) * (T1 x j s : ℝ) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> ring
  rw [this, h0, h1]
  ring

lemma guess_eq : magic_square_key_guess_success Ac MagicSquareConcave.ρc MagicSquareConcave.M0 = 1 := by
  rw [magic_square_key_guess_success, Finset.sum_eq_single (fun _ => false)]
  · have hA : Ac 0 (fun _ => false) = 1 := by
      rw [Ac, TA_key, map_nsmul, map_one, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      norm_num
    simp only [MagicSquareConcave.M0, if_true, hA, Matrix.one_kronecker_one, Matrix.one_mul]
    rw [MagicSquareConcave.perf_valid.2.2.2.2.2, Complex.one_re]
  · intro k _ hk
    simp [MagicSquareConcave.M0, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma perf_guess : magic_square_key_guess_success MagicSquareConcave.Ac MagicSquareConcave.ρc
    MagicSquareConcave.M0 = 1 / 4 := by
  rw [magic_square_key_guess_success, Finset.sum_eq_single (fun _ => false)]
  · simp only [MagicSquareConcave.M0, if_true]
    rw [MagicSquareConcave.perf_tr_rho]
    have ht : MagicSquareConcave.PA 0 (fun _ => false) 0 0 + MagicSquareConcave.PA 0 (fun _ => false) 1 1 +
        MagicSquareConcave.PA 0 (fun _ => false) 2 2 + MagicSquareConcave.PA 0 (fun _ => false) 3 3 = 4 := by
      decide +kernel
    have ht' := congrArg (Int.cast : ℤ → ℂ) ht
    push_cast at ht'
    have hc : (1 / 4 : ℂ) * ∑ a : Fin 4, ∑ a' : Fin 4,
        MagicSquareConcave.Ac 0 (fun _ => false) a a' * (1 : Matrix (Fin 4) (Fin 4) ℂ) a a' =
        ((1 / 4 : ℝ) : ℂ) := by
      simp only [MagicSquareConcave.Ac, Matrix.smul_apply, Matrix.one_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, eq_intCast, smul_eq_mul, Fin.sum_univ_four]
      simp
      linear_combination (1 / 4 : ℂ) * ht'
    rw [hc, Complex.ofReal_re]
  · intro k _ hk
    simp [MagicSquareConcave.M0, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

end MagicSquareGeLinear

theorem magic_square_guess_fn_ge_linear (δ : ℝ) (h0 : 0 ≤ δ)
    (h1 : δ ≤ 1 - magic_square_threshold_beta0) :
    1 - magic_square_guess_fn (magic_square_threshold_beta0 + δ) ≤
      3 * δ / (4 * (1 - magic_square_threshold_beta0)) := by
  have hs : Real.sqrt (2 / 3) = Real.sqrt 6 / 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    linear_combination (-1 / 9 : ℝ) * this
  have h6 : Real.sqrt 6 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hb : magic_square_threshold_beta0 = 2 / 3 + Real.sqrt 6 / 9 := by
    rw [magic_square_threshold_beta0, hs]; ring
  have hβ1 : magic_square_threshold_beta0 < 1 := by rw [hb]; linarith
  have gβ : 1 ≤ magic_square_guess_fn magic_square_threshold_beta0 := by
    rw [MagicSquareConcave.g_eq]
    refine le_csSup (MagicSquareConcave.gset_bdd _) ⟨4, 4, 1, MagicSquareGeLinear.Ac, MagicSquareGeLinear.Bc,
      MagicSquareConcave.ρc, MagicSquareConcave.M0, MagicSquareGeLinear.valid, MagicSquareConcave.M0_povm,
      ?_, MagicSquareGeLinear.guess_eq.symm⟩
    rw [MagicSquareGeLinear.score_eq, hb]
  have g1 : 1 / 4 ≤ magic_square_guess_fn 1 := by
    rw [MagicSquareConcave.g_eq]
    exact le_csSup (MagicSquareConcave.gset_bdd _) ⟨4, 4, 1, MagicSquareConcave.Ac, MagicSquareConcave.Bc,
      MagicSquareConcave.ρc, MagicSquareConcave.M0, MagicSquareConcave.perf_valid, MagicSquareConcave.M0_povm,
      MagicSquareConcave.score_one.ge, MagicSquareGeLinear.perf_guess.symm⟩
  have hpos : 0 < 1 - magic_square_threshold_beta0 := by linarith
  set l := δ / (1 - magic_square_threshold_beta0) with hl
  have hl0 : 0 ≤ l := div_nonneg h0 hpos.le
  have hl1 : l ≤ 1 := (div_le_one hpos).2 h1
  have hc := magic_square_guess_fn_concaveOn.2 (Set.mem_Iic.2 hβ1.le) (Set.mem_Iic.2 (le_refl (1 : ℝ)))
    (by linarith : (0 : ℝ) ≤ 1 - l) hl0 (by ring : (1 - l) + l = 1)
  simp only [smul_eq_mul] at hc
  have hx : (1 - l) * magic_square_threshold_beta0 + l * 1 = magic_square_threshold_beta0 + δ := by
    rw [hl]; field_simp; ring
  rw [hx] at hc
  have e1 := mul_le_mul_of_nonneg_left gβ (by linarith : (0 : ℝ) ≤ 1 - l)
  have e2 := mul_le_mul_of_nonneg_left g1 hl0
  have hgoal : 3 * δ / (4 * (1 - magic_square_threshold_beta0)) = 3 / 4 * l := by
    rw [hl]; field_simp
  rw [hgoal]
  linarith
