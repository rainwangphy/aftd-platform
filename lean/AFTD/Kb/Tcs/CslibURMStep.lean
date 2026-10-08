import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMState
import AFTD.Kb.Tcs.CslibURMInstr
import AFTD.Kb.Tcs.CslibURMRegsWrite
import AFTD.Kb.Tcs.CslibURMRegsRead
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr

/-!
# Cslib.URM.Step

Topic: computability   Node: c6f69411a59d

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Step`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Execution.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Single-step execution relation for URMs. Each constructor corresponds to one of the four instruction types: - `zero`: Execute `Z n` (set register n to 0) - `succ`: Execute `S n` (increment register n) - `transfer`: Execute `T m n` (copy register m to register n) - `jump_eq`: Execute `J m n q` when registers m and n are equal (jump to q) - `jump_ne`: Execute `J m n q` when registers m and n differ (proceed to next)
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable (p : Program) in
/-- Single-step execution relation for URMs. Each constructor corresponds to one of the four instruction types: - `zero`: Execute `Z n` (set register n to 0) - `succ`: Execute `S n` (increment register n) - `transfer`: Execute `T m n` (copy register m to register n) - `jump_eq`: Execute `J m n q` when registers m and n are equal (jump to q) - `jump_ne`: Execute `J m n q` when registers m and n differ (proceed to next) -/
@[grind]
inductive Cslib.URM.Step : State → State → Prop where
  | zero {s : State} {n : ℕ}
      (h : p[s.pc]? = some (Instr.Z n)) :
      Step s ⟨s.pc + 1, s.regs.write n 0⟩
  | succ {s : State} {n : ℕ}
      (h : p[s.pc]? = some (Instr.S n)) :
      Step s ⟨s.pc + 1, s.regs.write n (s.regs.read n + 1)⟩
  | transfer {s : State} {m n : ℕ}
      (h : p[s.pc]? = some (Instr.T m n)) :
      Step s ⟨s.pc + 1, s.regs.write n (s.regs.read m)⟩
  | jump_eq {s : State} {m n q : ℕ}
      (h : p[s.pc]? = some (Instr.J m n q))
      (heq : s.regs.read m = s.regs.read n) :
      Step s ⟨q, s.regs⟩
  | jump_ne {s : State} {m n q : ℕ}
      (h : p[s.pc]? = some (Instr.J m n q))
      (hne : s.regs.read m ≠ s.regs.read n) :
      Step s ⟨s.pc + 1, s.regs⟩
