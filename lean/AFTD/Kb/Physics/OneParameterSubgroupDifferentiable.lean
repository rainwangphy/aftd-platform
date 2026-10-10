import AFTD.Prelude
import AFTD.Kb.Physics.OneParameterSubgroupExistsIsUnitIntervalIntegral
import AFTD.Kb.Physics.OneParameterSubgroupMulIntervalIntegralEqSub

/-!
# OneParameterSubgroup.differentiable

Topic: classical_mechanics   Node: 962a73b07c1b

Provenance: formalization of a published result. Source: Physlib, `OneParameterSubgroup.differentiable`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

OneParameterSubgroup.differentiable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open OneParameterSubgroup in
open Filter Topology in
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E] in
lemma OneParameterSubgroup.differentiable [Nontrivial E] (U : AddChar ℝ E) (hU : Continuous U) :
    Differentiable ℝ U := by
  obtain ⟨d, _, hV⟩ := exists_isUnit_intervalIntegral U hU
  let V : E := ∫ x in (0 : ℝ)..d, U x
  let v : Eˣ := hV.unit
  have hv : (v : E) = V := hV.unit_spec
  let F : ℝ → E := fun t => ∫ x in (0 : ℝ)..t, U x
  have hF (t : ℝ) : HasDerivAt F (U t) t :=
    (hU.integral_hasStrictDerivAt 0 t).hasDerivAt
  have htranslate (t : ℝ) : U t * V = F (t + d) - F t :=
    mul_intervalIntegral_eq_sub U hU t d
  intro t
  have hR : HasDerivAt (fun s : ℝ => F (s + d) - F s)
      (U (t + d) - U t) t := by
    exact (HasDerivAt.comp_add_const t d (hF (t + d))).sub (hF t)
  have heq : U = fun s : ℝ => (F (s + d) - F s) * (↑v⁻¹ : E) := by
    funext s
    calc
      U s = (U s * (v : E)) * (↑v⁻¹ : E) := by simp
      _ = (F (s + d) - F s) * (↑v⁻¹ : E) := by rw [hv, htranslate]
  rw [heq]
  exact (hR.mul_const (↑v⁻¹ : E)).differentiableAt
