import AFTD.Prelude
import AFTD.Kb.Tcs.PrimeConvolutionChoi

/-!
# prime_convolution_choi_trace

Topic: quantum   Node: 3b903d28bd5f

Provenance: helper lemma. Sanity lemma for prime_convolution_choi, serving OP-2466: the Choi matrix of a trace-one environment has trace one.

For d ≥ 1, every r in ZMod d and every complex d×d matrix σ, the trace of prime_convolution_choi d r σ equals the trace of σ.
-/

open Finset

private theorem prime_convolution_choi_trace_inner_sum {d : ℕ} [NeZero d] (r : ZMod d)
    (σ : Matrix (Fin d) (Fin d) ℂ) (a j l : Fin d) :
    (∑ b : Fin d, if (b : ZMod d) = r * (a : ZMod d) + (j : ZMod d) ∧
                     (b : ZMod d) = r * (a : ZMod d) + (l : ZMod d) ∧
                     (a : ZMod d) + (j : ZMod d) = (a : ZMod d) + (l : ZMod d)
                  then σ j l else 0) =
    if j = l then σ j l else 0 := by
  split_ifs with hjl
  · subst hjl
    simp only [and_self, and_true]
    have hb : ∀ b : Fin d, ((b : ZMod d) = r * (a : ZMod d) + (j : ZMod d)) ↔
        b = ⟨(r * (a : ZMod d) + (j : ZMod d)).val, ZMod.val_lt _⟩ := by
      intro b
      constructor
      · intro h
        ext
        have hbval : ((b.val : ℕ) : ZMod d).val = b.val := ZMod.val_cast_of_lt b.is_lt
        rw [← hbval, h]
      · rintro rfl
        exact ZMod.natCast_zmod_val _
    simp_rw [hb]
    rw [sum_ite_eq', if_pos (mem_univ _)]
  · have hcond : ∀ b : Fin d, ¬ ((b : ZMod d) = r * (a : ZMod d) + (j : ZMod d) ∧
        (b : ZMod d) = r * (a : ZMod d) + (l : ZMod d) ∧
        (a : ZMod d) + (j : ZMod d) = (a : ZMod d) + (l : ZMod d)) := by
      intro b ⟨h1, h2, h3⟩
      have hjl_zmod : (j : ZMod d) = (l : ZMod d) := by
        exact add_left_cancel h3
      have hjl_fin : j = l := by
        ext
        have hjval : ((j.val : ℕ) : ZMod d).val = j.val := ZMod.val_cast_of_lt j.is_lt
        have hlval : ((l.val : ℕ) : ZMod d).val = l.val := ZMod.val_cast_of_lt l.is_lt
        rw [← hjval, ← hlval]
        exact congrArg ZMod.val hjl_zmod
      exact hjl hjl_fin
    have : (∑ b : Fin d, if (b : ZMod d) = r * (a : ZMod d) + (j : ZMod d) ∧
            (b : ZMod d) = r * (a : ZMod d) + (l : ZMod d) ∧
            (a : ZMod d) + (j : ZMod d) = (a : ZMod d) + (l : ZMod d)
         then σ j l else 0) = ∑ b : Fin d, (0 : ℂ) := by
      apply sum_congr rfl
      intro b _
      rw [if_neg (hcond b)]
    rw [this, sum_const_zero]

theorem prime_convolution_choi_trace (d : ℕ) [NeZero d] (r : ZMod d) (σ : Matrix (Fin d) (Fin d) ℂ) :
    (prime_convolution_choi d r σ).trace = σ.trace := by
  simp only [Matrix.trace, Matrix.diag, prime_convolution_choi, Matrix.of_apply]
  rw [← Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  have hswap : (∑ a : Fin d, ∑ b : Fin d, ∑ j : Fin d, ∑ l : Fin d,
      if (b : ZMod d) = r * (a : ZMod d) + (j : ZMod d) ∧
         (b : ZMod d) = r * (a : ZMod d) + (l : ZMod d) ∧
         (a : ZMod d) + (j : ZMod d) = (a : ZMod d) + (l : ZMod d) then σ j l else 0) =
      ∑ a : Fin d, ∑ j : Fin d, ∑ l : Fin d, ∑ b : Fin d,
      if (b : ZMod d) = r * (a : ZMod d) + (j : ZMod d) ∧
         (b : ZMod d) = r * (a : ZMod d) + (l : ZMod d) ∧
         (a : ZMod d) + (j : ZMod d) = (a : ZMod d) + (l : ZMod d) then σ j l else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [hswap]
  simp_rw [prime_convolution_choi_trace_inner_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [← mul_assoc, one_div_mul_cancel hd, one_mul]
