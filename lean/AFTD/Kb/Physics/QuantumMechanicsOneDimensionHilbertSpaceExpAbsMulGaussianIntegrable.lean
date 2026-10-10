import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceExpMulGaussianIntegrable
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumberExpSubOne

/-!
# QuantumMechanics.OneDimension.HilbertSpace.exp_abs_mul_gaussian_integrable

Topic: quantum_mechanics   Node: ff57cb418e9c

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.exp_abs_mul_gaussian_integrable`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Gaussians.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.exp_abs_mul_gaussian_integrable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open MeasureTheory in
lemma QuantumMechanics.OneDimension.HilbertSpace.exp_abs_mul_gaussian_integrable (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (|c * x|) * Real.exp (- b * x ^ 2)) := by
  rw [← MeasureTheory.integrableOn_univ]
  have h1 : Set.univ (α := ℝ) = (Set.Iic 0) ∪ Set.Ici 0 := (Set.Iic_union_Ici).symm
  rw [h1]
  apply MeasureTheory.IntegrableOn.union
  · let g := fun x => Real.exp ((- |c|) * x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Iic]
    · apply MeasureTheory.IntegrableOn.left_of_union (t := Set.Ici 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_gaussian_integrable b (- |c|) hb
    · intro x hx
      simp only [Set.mem_Iic] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, Real.exp_ne_zero, or_false, g]
      rw [abs_mul, abs_of_nonpos hx]
      ring
  · let g := fun x => Real.exp (|c| * x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Ici]
    · apply MeasureTheory.IntegrableOn.right_of_union (s := Set.Iic 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_gaussian_integrable b (|c|) hb
    · intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, Real.exp_ne_zero, or_false, g]
      rw [abs_mul, abs_of_nonneg hx]
