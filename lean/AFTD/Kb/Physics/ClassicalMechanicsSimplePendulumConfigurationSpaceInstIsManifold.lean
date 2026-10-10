import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstChartedSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceCircleHomeomorph
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceToCircleOfCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceOfCircleToCircle
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstT2Space
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstCompactSpace
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumConfigurationSpaceInstSecondCountableTopology

/-!
# ClassicalMechanics.SimplePendulum.ConfigurationSpace.instIsManifold

Topic: classical_mechanics   Node: 4c4162eaf7d4

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.SimplePendulum.ConfigurationSpace.instIsManifold`. Lean proof by Aadarsh Agarwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Geometric/Basic.lean (Copyright (c) 2026 Aadarsh Agarwal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The configuration space is an analytic manifold: every change of charts is a change of charts of the unit circle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Manifold ContDiff in
/-- The configuration space is an analytic manifold: every change of charts is a change of charts of the unit circle. -/
noncomputable instance ClassicalMechanics.SimplePendulum.ConfigurationSpace.instIsManifold : IsManifold (𝓡 1) ω' ConfigurationSpace where
  compatible := by
    rintro _ _ ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩
    -- The identification `h` with the circle is global, so `h.symm ≫ₕ h` is the identity.
    have hself : circleHomeomorph.toOpenPartialHomeomorph.symm.trans
        circleHomeomorph.toOpenPartialHomeomorph = OpenPartialHomeomorph.refl Circle := by
      rw [← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
        Homeomorph.symm_trans_self, Homeomorph.refl_toOpenPartialHomeomorph]
    -- Hence it cancels in the change of charts, which is therefore that of the circle.
    have hcancel : (circleHomeomorph.toOpenPartialHomeomorph.trans e₁).symm.trans
        (circleHomeomorph.toOpenPartialHomeomorph.trans e₂) = e₁.symm.trans e₂ := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
        ← OpenPartialHomeomorph.trans_assoc circleHomeomorph.toOpenPartialHomeomorph.symm,
        hself, OpenPartialHomeomorph.refl_trans]
    rw [hcancel]
    exact HasGroupoid.compatible he₁ he₂
