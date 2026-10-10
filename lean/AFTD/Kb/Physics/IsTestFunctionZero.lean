import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction

/-!
# IsTestFunction.zero

Topic: classical_mechanics   Node: 95c55abfd934

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.zero`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.zero
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
lemma IsTestFunction.zero :
    IsTestFunction (fun _ : X => (0 : U)) where
  smooth := by fun_prop
  supp := HasCompactSupport.zero
