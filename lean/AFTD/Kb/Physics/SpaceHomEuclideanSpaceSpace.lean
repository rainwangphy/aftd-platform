import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace
import AFTD.Kb.Physics.SpaceInstNontrivial

/-!
# Space.homEuclideanSpaceSpace

Topic: classical_mechanics   Node: d4d821bb6ff1

Provenance: formalization of a published result. Source: Physlib, `Space.homEuclideanSpaceSpace`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`Space d` is homoemorphic to d-dimensional euclidean space. This is used to define the `IsManifold` instance on `Space d`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold Real in
/-- `Space d` is homoemorphic to d-dimensional euclidean space. This is used to define the `IsManifold` instance on `Space d`. -/
noncomputable def Space.homEuclideanSpaceSpace (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃ₜ Space d where
  toFun v := ⟨EuclideanSpace.equiv (Fin d) ℝ v⟩
  invFun s := EuclideanSpace.equiv (Fin d) ℝ|>.symm s.val
  continuous_toFun := by
    rw [Metric.continuous_iff]
    intro b ε hε
    use ε
    simp_all [dist, Real.sqrt_eq_rpow]
  continuous_invFun := by
    rw [Metric.continuous_iff]
    intro b ε hε
    use ε
    simp_all [dist, Real.sqrt_eq_rpow]
