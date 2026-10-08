import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKIPolynomial
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.Polynomial.elimVar

Topic: computability   Node: a3ac3a34dd0b

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Polynomial.elimVar`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Basic.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Inductively define a polynomial `Γ'` so that (up to the fact that we haven't defined reduction on polynomials) `Γ' ⬝ t ↠ Γ[xₙ ← t]`.
-/

set_option quotPrecheck false
open Cslib Cslib.SKI
local infixl:100 " ⬝' " => SKI.Polynomial.app
local prefix:101 "&" => SKI.Polynomial.var
open Cslib Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- Inductively define a polynomial `Γ'` so that (up to the fact that we haven't defined reduction on polynomials) `Γ' ⬝ t ↠ Γ[xₙ ← t]`. -/
def Cslib.SKI.Polynomial.elimVar {n : Nat} : SKI.Polynomial (n+1) → SKI.Polynomial n
  /- The K-combinator leaves plain terms unchanged by substitution `K ⬝ x ⬝ t ⇒ x` -/
  | .term x => K ⬝' x
  /- Variables other than `xₙ` use the K-combinator as above, for `xₙ` we use `I`. -/
  | .var i => by
    by_cases i<n
    case pos h =>
      exact K ⬝' (.var <| @Fin.ofNat n ⟨Nat.ne_zero_of_lt h⟩ i)
    case neg h => exact ↑I
  /- The S-combinator inductively applies the substitution to the subterms of an application. -/
  | .app Γ Δ => S ⬝' Γ.elimVar ⬝' Δ.elimVar
