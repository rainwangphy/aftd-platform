import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringSingleTapeTMStmt
import AFTD.Kb.Tcs.CslibTuringSingleTapeTM

/-!
# Cslib.Turing.SingleTapeTM.inhabitedStmt

Topic: computability   Node: d29ee85969dc

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.SingleTapeTM.inhabitedStmt`. Lean proof by Bolton Bailey, Pim Spelier, Daan van Gent, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Turing.SingleTapeTM.inhabitedStmt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.SingleTapeTM in
open Relation in
open _root_.Turing in
variable {Symbol : Type} in
variable [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol) in
instance Cslib.Turing.SingleTapeTM.inhabitedStmt : Inhabited (Stmt Symbol) := inferInstance
