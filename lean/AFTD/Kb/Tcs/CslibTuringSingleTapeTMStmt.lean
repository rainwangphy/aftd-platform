import AFTD.Prelude

/-!
# Cslib.Turing.SingleTapeTM.Stmt

Topic: computability   Node: a71862cc6a29

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.SingleTapeTM.Stmt`. Lean proof by Bolton Bailey, Pim Spelier, Daan van Gent, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Turing machine "statement" is just a `Option`al command to move left or right, and write a symbol (i.e. an `Option Symbol`, where `none` is the blank symbol) on the `BiTape`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
open _root_.Turing in
variable {Symbol : Type} in
/-- A Turing machine "statement" is just a `Option`al command to move left or right, and write a symbol (i.e. an `Option Symbol`, where `none` is the blank symbol) on the `BiTape` -/
structure Cslib.Turing.SingleTapeTM.Stmt (Symbol : Type) where
  /-- The symbol to write at the current head position -/
  symbol : Option Symbol
  /-- The direction to move the tape head -/
  movement : Option Dir
deriving Inhabited
