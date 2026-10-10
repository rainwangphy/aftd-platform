import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionAddEquiv

/-!
# Physlib.Fin.involutionAddEquiv_cast

Topic: classical_mechanics   Node: e2e82ff5b418

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionAddEquiv_cast`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Fin.involutionAddEquiv_cast
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
lemma Physlib.Fin.involutionAddEquiv_cast {n : ℕ} {f1 f2 : {f : Fin n → Fin n // Function.Involutive f}}
    (hf : f1 = f2) :
    involutionAddEquiv f1 = (Equiv.subtypeEquivRight (by rw [hf]; simp)).trans
      ((involutionAddEquiv f2).trans (Equiv.optionCongr (finCongr (by rw [hf])))) := by
  subst hf
  rw [finCongr_refl, Equiv.optionCongr_refl]
  rfl
