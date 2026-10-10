import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction
import AFTD.Kb.Physics.IsTestFunctionCompLeft

/-!
# IsTestFunction.prod_fst

Topic: classical_mechanics   Node: 4a7a37f4f9cf

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.prod_fst`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.prod_fst
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V'} [NormedAddCommGroup V'] [NormedSpace ℝ V'] in
open ContDiff InnerProductSpace MeasureTheory in
@[fun_prop]
lemma IsTestFunction.prod_fst {f : X → U × V'} (hf : IsTestFunction f) :
    IsTestFunction (fun x => (f x).1) := by fun_prop (disch:=simp)
