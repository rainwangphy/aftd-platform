import AFTD.Prelude
import AFTD.Kb.Tcs.HermitianMatBridgePhi

/-!
# HermitianMatBridge.Φ_continuous

Topic: quantum   Node: 85a4d706804e

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMatBridge.Φ_continuous`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/LiebConcavity.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`Φ` is continuous (as a linear map between finite-dimensional spaces).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HermitianMatBridge in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- `Φ` is continuous (as a linear map between finite-dimensional spaces). -/
lemma HermitianMatBridge.Φ_continuous : Continuous (⇑Φ : Matrix d d ℂ → _) :=
  (Φ (d := d)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
