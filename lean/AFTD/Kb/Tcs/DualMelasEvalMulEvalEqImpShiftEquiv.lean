import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasShiftEquiv
import AFTD.Kb.Tcs.DualMelasIsNonDegenerate

/-!
# dual_melas_eval_mul_eval_eq_imp_shift_equiv

Topic: information   Node: 23bd0f5639b7

Provenance: helper lemma. arXiv:2610.38017 Lemma 5

Let $k \ge 3$, let $F$ be a finite field of order $2^k$, and let $\alpha \in F$ be a primitive $(2^k - 1)$-th root of unity. Let $f, g \in \mathbb{F}_2[X]$. If $f$ is non-degenerate with respect to $\alpha$ (i.e., $f(\alpha) \ne 0$ and $f(\alpha^{-1}) \ne 0$) and $f(\alpha) f(\alpha^{-1}) = g(\alpha) g(\alpha^{-1})$, then $f$ and $g$ are shift-equivalent modulo the product of the minimal polynomials over $\mathbb{F}_2$ of $\alpha$ and $\alpha^{-1}$ (that is, $\operatorname{minpoly}_{\mathbb{F}_2}(\alpha) \cdot \operatorname{minpoly}_{\mathbb{F}_2}(\alpha^{-1})$ divides $f - X^j g$ for some $j \in \mathbb{N}$).
-/

open Polynomial

lemma dual_melas_eval_mul_eval_eq_imp_shift_equiv_arith_key (k m : ℕ) (hk : 3 ≤ k) :
    ¬ (2^k - 1) ∣ (2^m + 1) := by
  set n := 2^k - 1 with hn
  have hn_pos : 0 < n := by
    have h8 : 8 ≤ 2^k := by
      calc 8 = 2^3 := by norm_num
        _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have h2k : (2^k) ≡ 1 [MOD n] := by
    rw [Nat.ModEq]
    have hkn : 2^k = n + 1 := by omega
    rw [hkn]
    simp
  have hreduce : (2^m) ≡ (2^(m % k)) [MOD n] := by
    conv_lhs => rw [← Nat.div_add_mod m k]
    rw [pow_add, pow_mul]
    have hp : (2^k)^(m/k) ≡ 1^(m/k) [MOD n] := Nat.ModEq.pow (m/k) h2k
    simp only [one_pow] at hp
    have := Nat.ModEq.mul hp (Nat.ModEq.refl (2^(m % k)))
    simpa using this
  intro h
  have hzero : (2^m + 1) ≡ 0 [MOD n] := by
    rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd h]
    simp
  have hred : (2^(m % k) + 1) ≡ 0 [MOD n] := by
    have h1 : (2^m + 1) ≡ (2^(m % k) + 1) [MOD n] :=
      Nat.ModEq.add hreduce (Nat.ModEq.refl 1)
    exact h1.symm.trans hzero
  have hdiv : n ∣ 2^(m % k) + 1 := by
    rw [Nat.ModEq] at hred
    exact Nat.dvd_of_mod_eq_zero hred
  have hr : m % k < k := Nat.mod_lt m (by omega)
  have hlt : 2^(m % k) + 1 < n := by
    have hle : 2^(m % k) ≤ 2^(k-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlt2 : 2^(k-1) + 1 < n := by
      have hk1 : k - 1 + 1 = k := by omega
      have hpow : 2^k = 2 * 2^(k-1) := by
        conv_lhs => rw [← hk1]
        rw [pow_succ']
      have hge : 4 ≤ 2^(k-1) := by
        calc 4 = 2^2 := by norm_num
          _ ≤ 2^(k-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hn2 : n = 2 * 2^(k-1) - 1 := by rw [hn, hpow]
      rw [hn2]; omega
    omega
  have hpos : 0 < 2^(m % k) + 1 := by positivity
  have hle' : n ≤ 2^(m % k) + 1 := Nat.le_of_dvd hpos hdiv
  exact absurd (hlt.trans_le hle') (lt_irrefl _)

lemma dual_melas_eval_mul_eval_eq_imp_shift_equiv_not_conj (k : ℕ) (hk : 3 ≤ k)
    (F : Type*) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (α : F) (hprim : IsPrimitiveRoot α (2^k - 1)) :
    ¬ IsConjRoot (ZMod 2) α α⁻¹ := by
  intro hconj
  obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv hconj
  have h8 : 8 ≤ 2^k := by
    calc 8 = 2^3 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hα0 : α ≠ 0 := (hprim.isUnit (by omega)).ne_zero
  have hmul : σ α * σ α⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hα0, map_one]
  have hσ' : σ α = α⁻¹ := by
    rw [hσ] at hmul
    exact eq_inv_of_mul_eq_one_left hmul
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F).2 σ
  have hi' : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ (i:ℕ) = σ := hi
  have hpow_eval : ∀ (t : ℕ), (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ t) α = α ^ (2 ^ t) := by
    intro t
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp
  have hval : α ^ (2 ^ (i:ℕ)) = α⁻¹ := by
    rw [← hpow_eval (i:ℕ), hi', hσ']
  have h1 : α ^ (2 ^ (i:ℕ) + 1) = 1 := by
    rw [pow_succ, hval, inv_mul_cancel₀ hα0]
  have hdvd : (2^k - 1) ∣ 2 ^ (i:ℕ) + 1 := hprim.dvd_of_pow_eq_one _ h1
  exact dual_melas_eval_mul_eval_eq_imp_shift_equiv_arith_key k (i:ℕ) hk hdvd

/-- Equal product of evaluations at α and α⁻¹ implies shift equivalence for non-degenerate f. -/
theorem dual_melas_eval_mul_eval_eq_imp_shift_equiv
    {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (k : ℕ) (hk : 3 ≤ k) (hcard : Fintype.card F = 2 ^ k)
    (α : F) (hprim : IsPrimitiveRoot α (2 ^ k - 1))
    (f g : Polynomial (ZMod 2))
    (hnondeg : dual_melas_is_non_degenerate α f)
    (heval : Polynomial.aeval α f * Polynomial.aeval α⁻¹ f =
      Polynomial.aeval α g * Polynomial.aeval α⁻¹ g) :
    dual_melas_shift_equiv α f g := by
  obtain ⟨hfu, hfv⟩ := hnondeg
  have h8 : 8 ≤ 2^k := by
    calc 8 = 2^3 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hα0 : α ≠ 0 := (hprim.isUnit (by omega)).ne_zero
  have huv : Polynomial.aeval α f * Polynomial.aeval α⁻¹ f ≠ 0 := mul_ne_zero hfu hfv
  have ha0 : Polynomial.aeval α g ≠ 0 := by
    intro h
    exact huv (by rw [heval, h, zero_mul])
  have hb0 : Polynomial.aeval α⁻¹ g ≠ 0 := by
    intro h
    exact huv (by rw [heval, h, mul_zero])
  have hne : (2^k - 1) ≠ 0 := by omega
  haveI : NeZero (2^k - 1) := ⟨hne⟩
  set w := Polynomial.aeval α f * (Polynomial.aeval α g)⁻¹ with hw_def
  have hw0 : w ≠ 0 := by
    rw [hw_def]
    exact mul_ne_zero hfu (inv_ne_zero ha0)
  have hwpow : w ^ (2^k - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one w hw0
    rwa [hcard] at h
  obtain ⟨j, hjlt, hj⟩ := hprim.eq_pow_of_pow_eq_one hwpow
  have hgoal1 : Polynomial.aeval α f = α^j * Polynomial.aeval α g := by
    rw [hj, hw_def, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  have hgoal2 : Polynomial.aeval α⁻¹ f = (α^j)⁻¹ * Polynomial.aeval α⁻¹ g := by
    rw [hj, hw_def, mul_inv_rev, inv_inv]
    calc Polynomial.aeval α⁻¹ f
        = (Polynomial.aeval α f)⁻¹ * (Polynomial.aeval α f * Polynomial.aeval α⁻¹ f) := by
          rw [← mul_assoc, inv_mul_cancel₀ hfu, one_mul]
      _ = (Polynomial.aeval α f)⁻¹ * (Polynomial.aeval α g * Polynomial.aeval α⁻¹ g) := by
          rw [heval]
      _ = Polynomial.aeval α g * (Polynomial.aeval α f)⁻¹ * Polynomial.aeval α⁻¹ g := by ring
  have hzα : Polynomial.aeval α (f - X^j * g) = 0 := by
    simp only [map_sub, map_mul, map_pow, aeval_X]
    rw [hgoal1, sub_self]
  have hzαinv : Polynomial.aeval α⁻¹ (f - X^j * g) = 0 := by
    simp only [map_sub, map_mul, map_pow, aeval_X]
    rw [inv_pow, hgoal2, sub_self]
  have hdvd1 : minpoly (ZMod 2) α ∣ f - X^j * g := minpoly.dvd (ZMod 2) α hzα
  have hdvd2 : minpoly (ZMod 2) α⁻¹ ∣ f - X^j * g := minpoly.dvd (ZMod 2) α⁻¹ hzαinv
  have hcop : IsCoprime (minpoly (ZMod 2) α) (minpoly (ZMod 2) α⁻¹) := by
    have hp : Irreducible (minpoly (ZMod 2) α) :=
      minpoly.irreducible (IsIntegral.of_finite (ZMod 2) α)
    have hq : Irreducible (minpoly (ZMod 2) α⁻¹) :=
      minpoly.irreducible (IsIntegral.of_finite (ZMod 2) α⁻¹)
    rw [Irreducible.coprime_iff_not_dvd hp]
    intro hdvd
    have hassoc : Associated (minpoly (ZMod 2) α) (minpoly (ZMod 2) α⁻¹) :=
      Irreducible.associated_of_dvd hp hq hdvd
    have heq : minpoly (ZMod 2) α = minpoly (ZMod 2) α⁻¹ :=
      Polynomial.eq_of_monic_of_associated
        (minpoly.monic (IsIntegral.of_finite (ZMod 2) α))
        (minpoly.monic (IsIntegral.of_finite (ZMod 2) α⁻¹)) hassoc
    exact dual_melas_eval_mul_eval_eq_imp_shift_equiv_not_conj k hk F α hprim heq
  exact ⟨j, hcop.mul_dvd hdvd1 hdvd2⟩
