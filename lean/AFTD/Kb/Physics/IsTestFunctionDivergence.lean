import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction
import AFTD.Kb.Physics.Divergence
import AFTD.Kb.Physics.DivergenceEqSumFderiv'
import AFTD.Kb.Physics.IsTestFunctionSum
import AFTD.Kb.Physics.IsTestFunctionCompLeft
import AFTD.Kb.Physics.IsTestFunctionFderivApply
import AFTD.Kb.Physics.DivergenceZero
import AFTD.Kb.Physics.IsTestFunctionContDiff

/-!
# IsTestFunction.divergence

Topic: classical_mechanics   Node: 9b18c497c55f

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.divergence`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.divergence
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V'} [NormedAddCommGroup V'] [NormedSpace ℝ V'] in
open ContDiff InnerProductSpace MeasureTheory in
@[fun_prop]
lemma IsTestFunction.divergence {f : X → X} [FiniteDimensional ℝ X] (hf : IsTestFunction f) :
    IsTestFunction (fun x => divergence ℝ f x) := by
  obtain ⟨s, ⟨bX⟩⟩ := Basis.exists_basis ℝ X
  have : Fintype s := FiniteDimensional.fintypeBasisIndex bX
  conv_rhs =>
    enter [x]
    rw [divergence_eq_sum_fderiv' bX]
  apply IsTestFunction.sum
  intro i
  let reprMap : X →ₗ[ℝ] ℝ := {
      toFun := (bX.repr · i)
      map_add' := by simp
      map_smul' := by simp

    }
  let f' : X →L[ℝ] ℝ := reprMap.toContinuousLinearMap
  have h_trace_contDiff : ContDiff ℝ ∞ f' := f'.contDiff
  change IsTestFunction (fun x => f' ((fderiv ℝ f x) (bX i)))
  apply IsTestFunction.comp_left
    (f:=fun x : X => (fderiv ℝ f x) (bX i)) (g:=f')
  · fun_prop
  · simp [f']
  · exact h_trace_contDiff
