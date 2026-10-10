import AFTD.Prelude
import AFTD.Kb.Physics.IsLocalizedFunctionTransform
import AFTD.Kb.Physics.IsLocalizedFunctionTransformId

/-!
# IsLocalizedFunctionTransform.deriv

Topic: classical_mechanics   Node: 65367dfe69b4

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform.deriv`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsLocalizedFunctionTransform.deriv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace MeasureTheory ContDiff in
variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasureSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {U}
  {V'} in
lemma IsLocalizedFunctionTransform.deriv [NormedAddCommGroup U] [NormedSpace ℝ U] :
    IsLocalizedFunctionTransform (fun φ : ℝ → U => deriv φ) := by
  intro K cK
  use (Metric.cthickening 1 K)
  constructor
  · exact IsCompact.cthickening cK
  · intro φ φ' hφ x hx
    dsimp
    have h : φ =ᶠ[nhds x] φ' := by
      apply Filter.eventuallyEq_of_mem (s := Metric.thickening 1 K)
      · apply Metric.isOpen_thickening.mem_nhds
        exact Metric.self_subset_thickening one_pos K hx
      · intro y hy
        exact hφ y (Metric.thickening_subset_cthickening 1 K hy)
    exact h.deriv_eq
