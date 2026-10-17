import AFTD.Prelude
import AFTD.Kb.Tcs.Mixable

/-!
# Mixable.mix_ab

Topic: information   Node: b43def392053

Provenance: formalization of a published result. Source: QuantumInfo, `Mixable.mix_ab`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Mixable.mix_ab
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Classical in
variable {T U : Type*} [AddCommMonoid U] [Module ℝ U] in
@[reducible]
noncomputable def Mixable.mix_ab [inst : Mixable U T] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x₁ x₂ : T) : T :=
  inst.mkT <| inst.convex
    (x := to_U x₁) (exists_apply_eq_apply _ _)
    (y := to_U x₂) (exists_apply_eq_apply _ _)
    ha hb hab
