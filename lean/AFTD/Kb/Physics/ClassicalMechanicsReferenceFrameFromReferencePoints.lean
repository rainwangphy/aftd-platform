import AFTD.Prelude
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace
import AFTD.Kb.Physics.SpaceInstNontrivial
import AFTD.Kb.Physics.SpaceInstChartedSpaceEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal
import AFTD.Kb.Physics.TimeInstChartedSpaceReal
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.ReferenceFrame.fromReferencePoints

Topic: classical_mechanics   Node: 8ab958070b73

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.fromReferencePoints`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Build a reference frame from the trajectories of a collection of reference points. At each time, the reference points must form an affine basis: none is redundant, and together they span the whole space. One reference point is chosen as the origin, and the displacements from it to the remaining points form the coordinate basis. The resulting frame need not be inertial or orthonormal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
variable {d : ℕ} in
/-- Build a reference frame from the trajectories of a collection of reference points. At each time, the reference points must form an affine basis: none is redundant, and together they span the whole space. One reference point is chosen as the origin, and the displacements from it to the remaining points form the coordinate basis. The resulting frame need not be inertial or orthonormal. -/
noncomputable def ClassicalMechanics.ReferenceFrame.fromReferencePoints
    (timeOrigin : Time)
    (referencePoints : Finset (Time → Space d))
    (independence : ∀ t, AffineIndependent ℝ fun point : referencePoints => point.val t)
    (spans_space : ∀ t, affineSpan ℝ {point.val t | point : referencePoints} = ⊤) :
    ReferenceFrame d :=
  let affineBasis (t : Time) : AffineBasis referencePoints ℝ (Space d) :=
    ⟨fun point => point.val t, independence t, spans_space t⟩
  let reference_points_not_empty := (affineBasis timeOrigin).nonempty
  let origin := Classical.choice reference_points_not_empty
  letI := Fintype.ofFinite {point : referencePoints // point ≠ origin}
  let basis t := (affineBasis t).basisOf origin
  let other_reference_points_size_eq_dim :
      Fintype.card {point : referencePoints // point ≠ origin} = d :=
    by simpa using (Module.finrank_eq_card_basis <| basis timeOrigin).symm
  let basisReindexed t :=
    (basis t).reindex (Fintype.equivFinOfCardEq other_reference_points_size_eq_dim)
  { timeOrigin := timeOrigin, origin := origin, basis := basisReindexed }
