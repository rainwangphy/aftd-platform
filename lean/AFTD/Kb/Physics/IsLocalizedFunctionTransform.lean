import AFTD.Prelude

/-!
# IsLocalizedFunctionTransform

Topic: classical_mechanics   Node: 89e521bc3ea6

Provenance: formalization of a published result. Source: Physlib, `IsLocalizedFunctionTransform`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsLocalizedfunctionTransform.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Function transformation `F` is localizable if the values of the transformed function `F φ` on some compact set `K` can depend only on the values of `φ` on some another compact set `L`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace MeasureTheory ContDiff in
variable
  {X} [NormedAddCommGroup X]
  {Y} [NormedAddCommGroup Y]
  {Z} [NormedAddCommGroup Z]
  {U}
  {V'}
  {W} in
/-- Function transformation `F` is localizable if the values of the transformed function `F φ` on some compact set `K` can depend only on the values of `φ` on some another compact set `L`. -/
def IsLocalizedFunctionTransform (F : (X → U) → (Y → V')) : Prop :=
  ∀ (K : Set Y) (_ : IsCompact K), ∃ L : Set X,
    IsCompact L ∧ ∀ (φ φ' : X → U), (∀ x ∈ L, φ x = φ' x) → ∀ x ∈ K, F φ x = F φ' x
