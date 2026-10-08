import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKIPolynomial
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKIPolynomialVarFreeToSKI
import AFTD.Kb.Tcs.CslibSKIPolynomialElimVar
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.Polynomial.toSKI

Topic: computability   Node: 9a7cc281addd

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Polynomial.toSKI`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Basic.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bracket abstraction, by induction using `SKI.Polynomial.elimVar`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- Bracket abstraction, by induction using `SKI.Polynomial.elimVar` -/
def Cslib.SKI.Polynomial.toSKI {n : Nat} (Γ : SKI.Polynomial n) : SKI :=
  match n with
  | 0 => Γ.varFreeToSKI
  | _ + 1 => Γ.elimVar.toSKI
