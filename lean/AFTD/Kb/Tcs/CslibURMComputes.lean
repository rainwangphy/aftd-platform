import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMEval
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram

/-!
# Cslib.URM.Computes

Topic: computability   Node: 6959423814ed

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Computes`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Computable.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A program `p` computes a partial function `f : (Fin n → ℕ) → Part ℕ` if for any input, `eval p inputs = f inputs` as partial values. This captures both: - The program halts iff the function is defined on that input - When both are defined, the program's output equals the function's value Note: Inputs are provided in registers 0, 1, ..., n-1 and output is read from register 0.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A program `p` computes a partial function `f : (Fin n → ℕ) → Part ℕ` if for any input, `eval p inputs = f inputs` as partial values. This captures both: - The program halts iff the function is defined on that input - When both are defined, the program's output equals the function's value Note: Inputs are provided in registers 0, 1, ..., n-1 and output is read from register 0. -/
def Cslib.URM.Computes (n : ℕ) (p : Program) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∀ inputs : Fin n → ℕ, eval p (List.ofFn inputs) = f inputs
