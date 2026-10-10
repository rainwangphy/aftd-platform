import AFTD.Prelude

/-!
# Equiv.sumEquivSigmalCond

Topic: classical_mechanics   Node: 8f68a0c3dd68

Provenance: formalization of a published result. Source: Physlib, `Equiv.sumEquivSigmalCond`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An alternative form of `Equiv.sumEquivSigmaBool` where `Bool.casesOn` is replaced by `cond`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped InnerProductSpace in
open Module in
/-- An alternative form of `Equiv.sumEquivSigmaBool` where `Bool.casesOn` is replaced by `cond`. -/
def Equiv.sumEquivSigmalCond : Fin m ⊕ Fin n ≃ Σ b, cond b (Fin m) (Fin n) :=
  calc Fin m ⊕ Fin n
    _ ≃ Fin n ⊕ Fin m := sumComm ..
    _ ≃ Σ b, bif b then (Fin m) else (Fin n) := sumEquivSigmaBool ..
    _ ≃ Σ b, cond b (Fin m) (Fin n) := sigmaCongrRight (fun | true | false => Equiv.refl _)
