import AFTD.Prelude
import AFTD.Kb.Tcs.Mixable

/-!
# Mixable.to_U_of_mkT

Topic: information   Node: a4e9a78b442a

Provenance: formalization of a published result. Source: QuantumInfo, `Mixable.to_U_of_mkT`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Mixable.to_U_of_mkT
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Classical in
variable {T U : Type*} [AddCommMonoid U] [Module ℝ U] in
@[simp]
theorem Mixable.to_U_of_mkT [inst : Mixable U T] (u : U) {h} : inst.to_U (mkT (u := u) h).1 = u :=
  (mkT (u := u) h).2
