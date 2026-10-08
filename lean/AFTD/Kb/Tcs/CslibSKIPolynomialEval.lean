import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKIPolynomial
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.Polynomial.eval

Topic: computability   Node: 9de8be90adcb

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Polynomial.eval`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Basic.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Substitute terms for the free variables of a polynomial
-/

open Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- Substitute terms for the free variables of a polynomial -/
def Cslib.SKI.Polynomial.eval {n : Nat} (Γ : SKI.Polynomial n) (l : List SKI) (hl : List.length l = n) :
    SKI :=
  match Γ with
  | .term x => x
  | .var i => l[i]
  | .app Γ Δ => (Γ.eval l hl) ⬝ (Δ.eval l hl)
