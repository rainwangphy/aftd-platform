import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibFLTSMtr
import AFTD.Kb.Tcs.CslibFLTSProd

/-!
# Cslib.FLTS.prod_mtr_eq

Topic: computability   Node: 338cc184835e

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLTS.prod_mtr_eq`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/Prod.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A state is reachable by the product FLTS iff its components are reachable by the respective FLTS components.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- A state is reachable by the product FLTS iff its components are reachable by the respective FLTS components. -/
@[simp, scoped grind =]
theorem Cslib.FLTS.prod_mtr_eq (flts1 : FLTS State1 Label) (flts2 : FLTS State2 Label)
    (s : State1 × State2) (μs : List Label) :
    (flts1.prod flts2).mtr s μs = (flts1.mtr s.fst μs, flts2.mtr s.snd μs) := by
  induction μs generalizing s <;> grind
