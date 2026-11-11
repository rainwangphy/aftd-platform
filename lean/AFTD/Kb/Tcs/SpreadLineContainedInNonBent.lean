import AFTD.Prelude
import AFTD.Kb.Tcs.NonzeroCubes
import AFTD.Kb.Tcs.NonBentComponents
import AFTD.Kb.Tcs.SpreadSubspace
import AFTD.Kb.Tcs.NonzeroCubesMul
import AFTD.Kb.Tcs.SubfieldNonzeroMemCubes
import AFTD.Kb.Tcs.SubfieldElementTraceZero
import AFTD.Kb.Tcs.ApnFamilyFaComponentEqCubic
import AFTD.Kb.Tcs.CubicPowerComponentCubeNonBent
import AFTD.Kb.Tcs.IsFieldBent
import AFTD.Kb.Tcs.ApnFamilyFa

/-!
# spread_line_contained_in_non_bent

Topic: cryptography   Node: 845ab4cbf5fd

Provenance: formalization of a published result. Source: arXiv:2611.10269 Proposition 11

Let E be a finite field equipped with an algebra structure over ZMod 2 such that the cardinality of E is 2^(2m), where m is an odd natural number. For any element a in nonzero_cubes E, the subspace spread_subspace E m a is contained in non_bent_components E m a ∪ {0}.
-/

set_option linter.style.haveILetI false in
theorem spread_line_contained_in_non_bent_mem_form {E : Type*} [Field E] [Algebra (ZMod 2) E]
    (m : ℕ) (a : E) {β : E} (hβ : β ∈ spread_subspace E m a) :
    ∃ t, t ^ (2^m) = t ∧ β = a * t := by
  haveI : CharP E 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have hpow : 2^m ≠ 0 := pow_ne_zero m (by norm_num)
  unfold spread_subspace at hβ
  refine Submodule.span_induction (p := fun x _ => ∃ t, t ^ (2^m) = t ∧ x = a * t) ?_ ?_ ?_ ?_ hβ
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · exact ⟨0, by rw [zero_pow hpow], by rw [mul_zero]⟩
  · rintro x y _ _ ⟨tx, htx, rfl⟩ ⟨ty, hty, rfl⟩
    exact ⟨tx + ty, by rw [add_pow_char_pow, htx, hty], by rw [mul_add]⟩
  · rintro c x _ ⟨t, ht, rfl⟩
    have hc : ((algebraMap (ZMod 2) E) c) ^ (2^m) = (algebraMap (ZMod 2) E) c := by
      rw [← map_pow]
      congr 1
      fin_cases c
      · show (0 : ZMod 2) ^ (2^m) = 0
        rw [zero_pow hpow]
      · show (1 : ZMod 2) ^ (2^m) = 1
        rw [one_pow]
    refine ⟨(algebraMap (ZMod 2) E) c * t, ?_, ?_⟩
    · rw [mul_pow, hc, ht]
    · rw [Algebra.smul_def]; ring

set_option linter.style.haveILetI false in
theorem spread_line_contained_in_non_bent_gen {E : Type*} [Field E] [Fintype E] [Algebra (ZMod 2) E]
    (m : ℕ) (hm : Odd m) (hcard : Fintype.card E = 2 ^ (2 * m)) (a : E) (ha : a ∈ nonzero_cubes E)
    {t : E} (htq : t ^ (2^m) = t) : a * t ∈ non_bent_components E m a ∪ {0} := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · obtain ⟨x, hx, hxa⟩ := ha
    have hacu : a ∈ nonzero_cubes E := ⟨x, hx, hxa⟩
    have ha0 : a ≠ 0 := by rw [← hxa]; exact pow_ne_zero 3 hx
    have hat_ne : a * t ≠ 0 := mul_ne_zero ha0 ht
    have ht_cube : t ∈ nonzero_cubes E := subfield_nonzero_mem_cubes m hm t ht htq
    have hat_cube : a * t ∈ nonzero_cubes E := nonzero_cubes_mul hacu ht_cube
    have htrace : Algebra.trace (ZMod 2) E ((a * t) * a⁻¹) = 0 := by
      have h : (a * t) * a⁻¹ = t := by
        field_simp
      rw [h]
      exact subfield_element_trace_zero m hcard t htq
    have hfun : (fun x => Algebra.trace (ZMod 2) E ((a * t) * apn_family_fa E a x))
        = (fun x => Algebra.trace (ZMod 2) E ((a * t) * x ^ 3)) := by
      funext x
      exact apn_family_fa_component_eq_cubic a (a * t) htrace x
    have hnb : ¬ is_field_bent E m (fun x => Algebra.trace (ZMod 2) E ((a * t) * apn_family_fa E a x)) := by
      rw [hfun]
      exact cubic_power_component_cube_non_bent m hcard (a * t) hat_cube
    exact Or.inl ⟨hat_ne, hnb⟩

/-- For odd m and a in C, the spread line subspace a F_q is contained in N_{F_a} ∪ {0}. -/
theorem spread_line_contained_in_non_bent {E : Type*} [Field E] [Fintype E] [Algebra (ZMod 2) E] (m : ℕ) (hm : Odd m) (hcard : Fintype.card E = 2 ^ (2 * m)) (a : E) (ha : a ∈ nonzero_cubes E) : (spread_subspace E m a : Set E) ⊆ non_bent_components E m a ∪ {0} := by
  intro β hβ
  obtain ⟨t, htq, rfl⟩ := spread_line_contained_in_non_bent_mem_form m a hβ
  exact spread_line_contained_in_non_bent_gen m hm hcard a ha htq
