import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionJointlyConvexOn

/-!
# GeneralizedPerspectiveFunction.JointlyConvex

Topic: quantum   Node: 27f0b5e6b979

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.JointlyConvex`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Joint convexity of a two-variable map without domain restrictions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GeneralizedPerspectiveFunction in
universe u in
variable {E F G : Type*} in
variable [AddCommMonoid E] [Module ℝ E] in
variable [AddCommMonoid F] [Module ℝ F] in
variable [Preorder G] [AddCommMonoid G] [Module ℝ G] in
/-- Joint convexity of a two-variable map without domain restrictions. -/
def GeneralizedPerspectiveFunction.JointlyConvex (Φ : E → F → G) : Prop :=
  JointlyConvexOn (Set.univ : Set E) (Set.univ : Set F) Φ
