import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKIPolynomial
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKIPolynomialEval
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.Polynomial.varFreeToSKI

Topic: computability   Node: 5af39fd085bd

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Polynomial.varFreeToSKI`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Basic.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A polynomial with no free variables is a term
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- A polynomial with no free variables is a term -/
def Cslib.SKI.Polynomial.varFreeToSKI (Γ : SKI.Polynomial 0) : SKI := Γ.eval [] (by trivial)
