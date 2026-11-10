import AFTD.Prelude
import AFTD.Kb.Tcs.NonzeroCubes
import AFTD.Kb.Tcs.IsFieldBent
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.TraceWalshCoeff
import AFTD.Kb.Tcs.V

/-!
# cubic_power_component_cube_non_bent

Topic: cryptography   Node: 689680255b7a

Provenance: helper lemma. arXiv:2611.10269 Sec. 7 (Göloğlu and Pavlů, 2021, Lemma 1)

Let E be a finite field of characteristic 2 with 2^(2m) elements. If β in E is a nonzero cube, then the Boolean function x ↦ Tr(β x^3) is not bent.
-/

private def cubic_sign (t : ZMod 2) : ℤ := if t = 0 then 1 else -1

private lemma cubic_sign_add_one (u : ZMod 2) : cubic_sign (u + 1) = -cubic_sign u := by
  revert u; decide

private lemma cubic_zmod_two_eq_one : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide

private lemma cubic_zmod_two_add_self : ∀ t : ZMod 2, t + t = 0 := by decide

private lemma cubic_sum_eq_zero_of_neg {G : Type*} [AddGroup G] [Fintype G] (a : G) (F : G → ℤ)
    (h : ∀ x, F (x + a) = -F x) : ∑ x, F x = 0 := by
  have he := Fintype.sum_equiv (Equiv.addRight a) (fun x => F (x + a)) F (fun x => rfl)
  have h2 : ∑ x : G, F (x + a) = ∑ x : G, -F x := Finset.sum_congr rfl (fun x _ => h x)
  rw [h2, Finset.sum_neg_distrib] at he
  have h3 : (∑ x : G, F x) = -(∑ x : G, F x) := he.symm
  linarith

private lemma cubic_trace_sq_eq {E : Type*} [Field E] [Fintype E] [Algebra (ZMod 2) E] (y : E) :
    Algebra.trace (ZMod 2) E (y ^ 2) = Algebra.trace (ZMod 2) E y := by
  apply FaithfulSMul.algebraMap_injective (ZMod 2) E
  rw [FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) E (y ^ 2),
      FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) E y]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  have heq : ∀ i, (y ^ 2) ^ (2 ^ i) = y ^ (2 ^ (i + 1)) := by
    intro i
    rw [← pow_mul, ← pow_succ' 2 i]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range _) => heq i)]
  have htel : ∑ i ∈ Finset.range (Module.finrank (ZMod 2) E),
      ((fun k => y ^ (2 ^ k)) (i + 1) - (fun k => y ^ (2 ^ k)) i)
        = (fun k => y ^ (2 ^ k)) (Module.finrank (ZMod 2) E) - (fun k => y ^ (2 ^ k)) 0 :=
    Finset.sum_range_sub (fun k => y ^ (2 ^ k)) (Module.finrank (ZMod 2) E)
  simp only at htel
  rw [Finset.sum_sub_distrib] at htel
  have hc : 2 ^ Module.finrank (ZMod 2) E = Fintype.card E := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := E), ZMod.card]
  have hlast : y ^ (2 ^ Module.finrank (ZMod 2) E) = y ^ (2 ^ 0) := by
    rw [pow_zero, pow_one, hc]; exact FiniteField.pow_card y
  rw [hlast, sub_self] at htel
  exact sub_eq_zero.mp htel

private lemma cubic_trace_one_eq_zero {E : Type*} [Field E] [Fintype E] [Algebra (ZMod 2) E]
    (m : ℕ) (hcard : Fintype.card E = 2 ^ (2 * m)) : Algebra.trace (ZMod 2) E (1 : E) = 0 := by
  have hfin : Module.finrank (ZMod 2) E = 2 * m := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [ZMod.card] at h
    rw [hcard] at h
    exact Nat.pow_right_injective (by norm_num) h.symm
  rw [← map_one (algebraMap (ZMod 2) E), Algebra.trace_algebraMap, hfin]
  have h2 : (2 : ℕ) • (1 : ZMod 2) = 0 := by
    rw [two_nsmul]
    exact (by decide : (1 : ZMod 2) + 1 = 0)
  calc (2 * m) • (1 : ZMod 2) = m • ((2 : ℕ) • (1 : ZMod 2)) := by rw [mul_nsmul]
    _ = m • 0 := by rw [h2]
    _ = 0 := smul_zero m

private lemma cubic_cube_expand {E : Type*} [Field E] [CharP E 2] (x c : E) (hc0 : c ≠ 0) :
    c ^ 3 * (x + c⁻¹) ^ 3 + c ^ 3 * x ^ 3 = (c * x) ^ 2 + (c * x) + 1 := by
  have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have h3 : (3 : E) = 1 := by
    have h23 : (3 : E) = (2 : E) + 1 := by norm_num
    rw [h23, h2, zero_add]
  have hce : c ^ 3 * (x + c⁻¹) ^ 3 = c ^ 3 * x ^ 3 + (c ^ 2 * x ^ 2 + c * x + 1) := by
    have e1 : c ^ 3 * (x + c⁻¹) ^ 3 = (c * x + 1) ^ 3 := by
      rw [← mul_pow]
      congr 1
      rw [mul_add, mul_inv_cancel₀ hc0]
    rw [e1]
    have e2 : (c * x + 1) ^ 3 = (c * x) ^ 3 + ((c * x) ^ 2 + c * x + 1) := by
      ring_nf; rw [h3]; ring
    rw [e2]; ring
  rw [hce]
  have hAA : c ^ 3 * x ^ 3 + c ^ 3 * x ^ 3 = 0 := by rw [← two_mul, h2, zero_mul]
  calc c ^ 3 * x ^ 3 + (c ^ 2 * x ^ 2 + c * x + 1) + c ^ 3 * x ^ 3
      = (c ^ 2 * x ^ 2 + c * x + 1) + (c ^ 3 * x ^ 3 + c ^ 3 * x ^ 3) := by ring
    _ = (c ^ 2 * x ^ 2 + c * x + 1) + 0 := by rw [hAA]
    _ = (c * x) ^ 2 + (c * x) + 1 := by rw [add_zero]; ring

private lemma cubic_exists_trace_mul_ne_zero {E : Type*} [Field E] [Fintype E] [Algebra (ZMod 2) E]
    (a : E) (ha : a ≠ 0) : ∃ α : E, Algebra.trace (ZMod 2) E (α * a) ≠ 0 := by
  by_contra h
  push Not at h
  exact ha ((traceForm_nondegenerate (ZMod 2) E).2 a (fun y => by
    rw [Algebra.traceForm_apply]; exact h y))

/-- The cubic component function x ↦ Tr(β x^3) is non-bent whenever β is a nonzero cube. -/
theorem cubic_power_component_cube_non_bent {E : Type*} [Field E] [Fintype E] [Algebra (ZMod 2) E] (m : ℕ) (hcard : Fintype.card E = 2 ^ (2 * m)) (β : E) (hβ : β ∈ nonzero_cubes E) : ¬ is_field_bent E m (fun x => Algebra.trace (ZMod 2) E (β * x ^ 3)) := by
  intro hbent
  simp only [nonzero_cubes, Set.mem_ofPred_eq] at hβ
  obtain ⟨c, hc0, hcβ⟩ := hβ
  haveI hc2 : CharP E 2 :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (ZMod 2) E) 2
  have hkey : ∀ x : E, Algebra.trace (ZMod 2) E (β * (x + c⁻¹) ^ 3)
      = Algebra.trace (ZMod 2) E (β * x ^ 3) := by
    intro x
    have hsum : Algebra.trace (ZMod 2) E (β * (x + c⁻¹) ^ 3)
        + Algebra.trace (ZMod 2) E (β * x ^ 3) = 0 := by
      rw [← map_add]
      have harg : β * (x + c⁻¹) ^ 3 + β * x ^ 3 = (c * x) ^ 2 + (c * x) + 1 := by
        rw [← hcβ]; exact cubic_cube_expand x c hc0
      rw [harg]
      have hsq := cubic_trace_sq_eq (E := E) (c * x)
      have hone := cubic_trace_one_eq_zero (E := E) m hcard
      rw [show (c * x) ^ 2 + (c * x) + 1 = ((c * x) ^ 2 + (c * x)) + 1 from by ring,
        map_add, map_add, hsq, hone, add_zero]
      exact cubic_zmod_two_add_self _
    have hBB := cubic_zmod_two_add_self (Algebra.trace (ZMod 2) E (β * x ^ 3))
    calc Algebra.trace (ZMod 2) E (β * (x + c⁻¹) ^ 3)
        = Algebra.trace (ZMod 2) E (β * (x + c⁻¹) ^ 3) + 0 := by rw [add_zero]
      _ = Algebra.trace (ZMod 2) E (β * (x + c⁻¹) ^ 3)
            + (Algebra.trace (ZMod 2) E (β * x ^ 3) + Algebra.trace (ZMod 2) E (β * x ^ 3)) := by
            rw [hBB]
      _ = (Algebra.trace (ZMod 2) E (β * (x + c⁻¹) ^ 3)
            + Algebra.trace (ZMod 2) E (β * x ^ 3)) + Algebra.trace (ZMod 2) E (β * x ^ 3) := by
            ring
      _ = 0 + Algebra.trace (ZMod 2) E (β * x ^ 3) := by rw [hsum]
      _ = Algebra.trace (ZMod 2) E (β * x ^ 3) := by rw [zero_add]
  obtain ⟨α, hα⟩ := cubic_exists_trace_mul_ne_zero (E := E) c⁻¹ (inv_ne_zero hc0)
  have hα1 : Algebra.trace (ZMod 2) E (α * c⁻¹) = 1 := cubic_zmod_two_eq_one _ hα
  have hstep : ∀ x : E,
      cubic_sign (Algebra.trace (ZMod 2) E (β * (x + c⁻¹) ^ 3)
              + Algebra.trace (ZMod 2) E (α * (x + c⁻¹)))
        = -cubic_sign (Algebra.trace (ZMod 2) E (β * x ^ 3) + Algebra.trace (ZMod 2) E (α * x)) := by
    intro x
    have hfa := hkey x
    have htr : Algebra.trace (ZMod 2) E (α * (x + c⁻¹))
        = Algebra.trace (ZMod 2) E (α * x) + 1 := by
      rw [mul_add, map_add, hα1]
    rw [hfa, htr,
      show Algebra.trace (ZMod 2) E (β * x ^ 3) + (Algebra.trace (ZMod 2) E (α * x) + 1)
          = (Algebra.trace (ZMod 2) E (β * x ^ 3) + Algebra.trace (ZMod 2) E (α * x)) + 1
          from by ring]
    exact cubic_sign_add_one _
  have hzero : trace_walsh_coeff E (fun x => Algebra.trace (ZMod 2) E (β * x ^ 3)) α = 0 := by
    rw [show trace_walsh_coeff E (fun x => Algebra.trace (ZMod 2) E (β * x ^ 3)) α
        = ∑ x, cubic_sign (Algebra.trace (ZMod 2) E (β * x ^ 3)
            + Algebra.trace (ZMod 2) E (α * x)) from rfl]
    exact cubic_sum_eq_zero_of_neg c⁻¹ _ hstep
  have h1 := hbent α
  rw [hzero, abs_zero] at h1
  have hpos : (0:ℤ) < 2 ^ m := by positivity
  linarith
