import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionAddEquiv

/-!
# Physlib.Fin.involutionAddEquiv_cast'

Topic: classical_mechanics   Node: ff5043c77f44

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionAddEquiv_cast'`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Fin.involutionAddEquiv_cast'
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
lemma Physlib.Fin.involutionAddEquiv_cast' {m : ℕ} {f1 f2 : {f : Fin m → Fin m // Function.Involutive f}}
    {N : ℕ} (hf : f1 = f2) (n : Option (Fin N))
    (hn1 : N = (Finset.filter (fun i => f1.1 i = i) Finset.univ).card)
    (hn2 : N = (Finset.filter (fun i => f2.1 i = i) Finset.univ).card) :
    HEq ((involutionAddEquiv f1).symm (Option.map (finCongr hn1) n))
    ((involutionAddEquiv f2).symm (Option.map (finCongr hn2) n)) := by
  subst hf
  rfl
