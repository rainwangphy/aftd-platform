import AFTD.Prelude

/-!
# GeneralizedPerspectiveFunction.JointlyConvexOn

Topic: quantum   Node: 35a73cd14593

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.JointlyConvexOn`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Joint convexity of a two-variable map on prescribed domains in each argument.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {E F G : Type*} in
variable [AddCommMonoid E] [Module ℝ E] in
variable [AddCommMonoid F] [Module ℝ F] in
variable [Preorder G] [AddCommMonoid G] [Module ℝ G] in
/-- Joint convexity of a two-variable map on prescribed domains in each argument. -/
def GeneralizedPerspectiveFunction.JointlyConvexOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)
      ≤ (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂
