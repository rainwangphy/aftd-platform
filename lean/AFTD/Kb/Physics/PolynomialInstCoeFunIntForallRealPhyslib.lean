import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialRealEval

/-!
# Polynomial.instCoeFunIntForallReal_physlib

Topic: classical_mechanics   Node: b3777beb4a67

Provenance: formalization of a published result. Source: Physlib, `Polynomial.instCoeFunIntForallReal_physlib`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.instCoeFunIntForallReal_physlib
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
noncomputable instance Polynomial.instCoeFunIntForallReal_physlib : CoeFun (Polynomial ℤ) (fun _ ↦ ℝ → ℝ) := ⟨realEval⟩
