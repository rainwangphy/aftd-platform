import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTSCat

Topic: computability   Node: 8104b54d4972

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTSCat`. Lean proof by Ayberk Tosun, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/LTSCat/Basic.lean (Copyright (c) 2026 Ayberk Tosun (Zeroth Research). All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The definition of labelled transition system (with the type of states and the type of labels as part of the structure).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
set_option linter.checkUnivs false in
/-- The definition of labelled transition system (with the type of states and the type of labels as part of the structure). -/
structure Cslib.LTSCat : Type (max u v + 1) where
  /-- Type of states of an LTS -/
  State : Type u
  /-- Type of labels of an LTS -/
  Label : Type v
  /-- Transition relation of an LTS -/
  lts : LTS State Label
