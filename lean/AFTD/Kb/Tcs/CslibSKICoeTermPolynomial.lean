import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKIPolynomial

/-!
# Cslib.SKI.CoeTermPolynomial

Topic: computability   Node: d942d7cb84e2

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.CoeTermPolynomial`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Basic.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.SKI.CoeTermPolynomial
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
instance Cslib.SKI.CoeTermPolynomial (n : Nat) : Coe SKI (SKI.Polynomial n) := ⟨SKI.Polynomial.term⟩
