import AFTD.Prelude

/-!
# Cslib.URM.Instr

Topic: computability   Node: 0532320b5c45

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Instr`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

URM instructions. - `Z n`: Set register n to zero - `S n`: Increment register n by one - `T m n`: Transfer (copy) the contents of register m to register n - `J m n q`: If registers m and n have equal contents, jump to instruction q; otherwise proceed to the next instruction
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- URM instructions. - `Z n`: Set register n to zero - `S n`: Increment register n by one - `T m n`: Transfer (copy) the contents of register m to register n - `J m n q`: If registers m and n have equal contents, jump to instruction q; otherwise proceed to the next instruction -/
@[grind]
inductive Cslib.URM.Instr : Type where
  | Z : ℕ → Instr
  | S : ℕ → Instr
  | T : ℕ → ℕ → Instr
  | J : ℕ → ℕ → ℕ → Instr
deriving DecidableEq, Repr
