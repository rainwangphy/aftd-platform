import AFTD.Prelude

/-!
# Space.integrable_neg_pow_on_ioi

Topic: classical_mechanics   Node: 4c60b2d0d202

Provenance: formalization of a published result. Source: Physlib, `Space.integrable_neg_pow_on_ioi`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Integrals/RadialAngularMeasure.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.integrable_neg_pow_on_ioi
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal Real in
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] in
variable [NormedSpace ℝ E] [NormedSpace ℝ F] in
open MeasureTheory in
lemma Space.integrable_neg_pow_on_ioi (n : ℕ) :
    IntegrableOn (fun x : ℝ => (|((1 : ℝ) + x) ^ (- (n + 2) : ℝ)|)) (Set.Ioi 0) := by
  have hpre : (fun x : ℝ => (1 : ℝ) + x) ⁻¹' Set.Ioi 1 = Set.Ioi 0 := by
    ext x
    simp
  have integrableOn_rpow_neg :
      IntegrableOn (fun x : ℝ => ((1 : ℝ) + x) ^ (- (n + 2) : ℝ)) (Set.Ioi 0) := by
    rw [← hpre]
    exact ((measurePreserving_add_left volume (1 : ℝ)).integrableOn_comp_preimage
      (measurableEmbedding_addLeft 1)
      (f := fun y : ℝ => y ^ (- (n + 2) : ℝ)) (s := Set.Ioi 1)).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith [Nat.cast_nonneg (α := ℝ) n]) one_pos)
  refine integrableOn_rpow_neg.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hx
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
