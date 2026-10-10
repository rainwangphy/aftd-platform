import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumber
import AFTD.Kb.Physics.CondensedMatterTightBindingChainInstNeZeroNatN
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumberExpN

/-!
# CondensedMatter.TightBindingChain.quantaWaveNumber_exp_sub_one

Topic: condensed_matter   Node: a3f324621765

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_sub_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CondensedMatter.TightBindingChain.quantaWaveNumber_exp_sub_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter CondensedMatter.TightBindingChain in
open InnerProductSpace in
variable (T : TightBindingChain) in
lemma CondensedMatter.TightBindingChain.quantaWaveNumber_exp_sub_one (n : Fin T.N) (k : T.QuantaWaveNumber) :
    Complex.exp (Complex.I * k * (n - 1).val * T.a) =
    Complex.exp (Complex.I * k * n * T.a) * Complex.exp (- Complex.I * k * T.a) := by
  rw [Fin.val_sub]
  trans Complex.exp (Complex.I * ↑↑k * ↑(((T.N - 1 + n)/T.N) * T.N + (n - 1).val) * ↑T.a)
  · simp only [Nat.cast_add, Nat.cast_mul]
    have h0 : (Complex.I * ↑↑k * (↑((T.N - 1 + ↑n) / T.N) * ↑T.N + (n - 1).val) * ↑T.a)
        = Complex.I * ↑↑k * ↑((T.N - 1 + ↑n) / T.N) * ↑T.N * ↑T.a +
        Complex.I * ↑↑k * ((n - 1).val* ↑T.a) := by ring
    rw [h0, Complex.exp_add, quantaWaveNumber_exp_N]
    simp only [Fin.val_one', one_mul]
    congr 1
    simp only [mul_assoc, mul_eq_mul_left_iff, mul_eq_mul_right_iff, Nat.cast_inj,
      Complex.ofReal_eq_zero, Complex.I_ne_zero, or_false]
    aesop
  · have hx : (((T.N - 1 + n)/T.N) * T.N + (n - 1).val) =
        (T.N - 1 + n) := by
      conv_rhs => rw [← Nat.div_add_mod' (a := T.N - 1 + n) (b := T.N)]
      congr
      by_cases hn : T.N = 1
      · simp only [hn, tsub_self, zero_add]
        have h0 : n = 0 := by omega
        subst h0
        simpa using hn
      · rw [@Fin.val_sub]
        congr
        simp [Nat.one_mod_eq_one.mpr hn]
    rw [hx]
    have hl : (Complex.I * ↑↑k * ↑(T.N - 1 + ↑n) * ↑T.a) =
        Complex.I * ↑↑k * n * ↑T.a + Complex.I * ↑↑k * ↑(T.N - 1) * ↑T.a := by
      simp only [Nat.cast_add]
      ring
    rw [hl, Complex.exp_add]
    congr 1
    rw [Nat.cast_pred (Nat.pos_of_neZero T.N)]
    have hl : (Complex.I * ↑↑k * (↑T.N - 1) * ↑T.a) =
      Complex.I * ↑↑k * (1 : ℕ) * ↑T.N * ↑T.a + (- Complex.I * ↑↑k * ↑T.a) := by ring
    rw [hl, Complex.exp_add, quantaWaveNumber_exp_N, neg_mul, one_mul]
