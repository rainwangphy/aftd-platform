import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionJointlyConcaveOn

/-!
# GeneralizedPerspectiveFunction.JointlyConcave

Topic: quantum   Node: 32023c173133

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.JointlyConcave`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Joint concavity of a two-variable map without domain restrictions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GeneralizedPerspectiveFunction in
universe u in
variable {E F G : Type*} in
variable [AddCommMonoid E] [Module ℝ E] in
variable [AddCommMonoid F] [Module ℝ F] in
variable [Preorder G] [AddCommMonoid G] [Module ℝ G] in
/-- Joint concavity of a two-variable map without domain restrictions. -/
def GeneralizedPerspectiveFunction.JointlyConcave (Φ : E → F → G) : Prop :=
  JointlyConcaveOn (Set.univ : Set E) (Set.univ : Set F) Φ
