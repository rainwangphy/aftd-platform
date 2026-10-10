import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction

/-!
# IsTestFunction.integrable

Topic: classical_mechanics   Node: 5028cc726a98

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.integrable`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.integrable
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
lemma IsTestFunction.integrable [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → U} (hf : IsTestFunction f)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] :
    MeasureTheory.Integrable f μ :=
  Continuous.integrable_of_hasCompactSupport (continuous hf.smooth) hf.supp
