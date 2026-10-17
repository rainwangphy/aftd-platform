import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand

/-!
# measurable_complexLaplaceIntegrand

Topic: quantum   Node: 825a88ba2ecb

Provenance: formalization of a published result. Source: QuantumInfo, `measurable_complexLaplaceIntegrand`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

measurable_complexLaplaceIntegrand
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem measurable_complexLaplaceIntegrand
    {α : Type*} [MeasurableSpace α] {E : α → WithTop ℝ} (hE : Measurable E) (z : ℂ) :
    Measurable (ComplexLaplaceIntegrand E z) := by
  rw [show ComplexLaplaceIntegrand E z =
      fun x => if E x = ⊤ then 0 else Complex.exp (-z * (((E x).untopD 0 : ℝ) : ℂ)) by
    funext x
    unfold ComplexLaplaceIntegrand
    by_cases hx : E x = ⊤
    · simp [hx]
    · simp only [hx, dite_false, ite_false]
      congr 2
      let y := E x
      have hy : y ≠ ⊤ := by simpa [y] using hx
      change ((y.untop hy : ℝ) : ℂ) = ((y.untopD 0 : ℝ) : ℂ)
      obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp hy
      have hUntop : y.untop hy = e := by
        apply WithTop.coe_inj.mp
        rw [WithTop.coe_untop, ← he]
      have hUntopD : y.untopD 0 = e := by
        rw [← he]
        rfl
      rw [hUntop, hUntopD]]
  exact Measurable.ite (hE (measurableSet_singleton (⊤ : WithTop ℝ))) measurable_const
    (Complex.continuous_exp.measurable.comp (by fun_prop :
      Measurable fun x => -z * (((E x).untopD 0 : ℝ) : ℂ)))
